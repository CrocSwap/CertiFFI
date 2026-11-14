import ArmCertWalk.SuffixNoFault
import ArmCertWalk.LeafOutputData
import ArmCertWalk.WalkEndpoint

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

def walkAddress : WalkVars → AddressDescriptor | (_, _, _, _, _, _, _, _, address, _) => address

/-- The SAME actual loop endpoint supplies all suffix inputs. Current image
readiness is recovered after the ordered table stores; no leaf call is rerun. -/
theorem endpoint_suffix_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (va : BitVec 64) (acc : AccessDescriptor)
    (context : TLBContext) (entry : TLBRecord) (level : Nat)
    (physicalSlot : FullAddress) (view : S1DescriptorPIE.View 64)
    (prior : S1LogicalReference.TablePermissions) (overlay : Bool) (out : WalkVars) (state : State)
    (format : WalkFormat spec.params spec.physicalConfig spec.controls)
    (physical : PhysicalAt spec.physicalConfig state)
    (cache : state.regs.bank_Bool .__tlb_enabled = false)
    (image : TopologyImageAt spec state)
    (used : rowsObserve spec.imageRows physicalSlot.address.toNat true view)
    (positive : 1 ≤ level) (valid : level ≤ 3)
    (admissible : LeafSuffixAdmissible spec.physicalConfig state.regs va level view)
    (endpoint : WalkLeafEndpoint spec.params config spec.controls overlay
      level physicalSlot view prior out state) :
    ∃ other,
      S1WalkSuffixSource.suffix spec.params va .Regime_EL20 acc 64 context entry out state =
        .ok (.ok (walkFault out, walkAddress out, walkCurrent out, walkDescriptor out)) other ∧
      WalkLeafEndpoint spec.params config spec.controls overlay level physicalSlot view prior out other ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  have endpointSaved := endpoint
  obtain ⟨current, descriptor, currentLevel, currentDisCH, priorEq, rawView,
    bytes, descriptorEq, slotEq, stop, noFault, meaning⟩ := endpoint
  obtain ⟨raw, currentBytes, currentView, ready⟩ := image _ true view used
  have rawEq : raw = descriptor := S1ByteMemory.descriptor_unique _ _ _ _ currentBytes bytes
  subst raw
  have afReady := (afReady_iff spec.params .leaf descriptor).mpr ready
  obtain ⟨noNT, outputBound⟩ := leaf_suffix_data_actual spec.physicalConfig state.regs va level view
    _ _ _ descriptor rawView admissible
  have output := leaf_meaning_output config spec.controls spec.params overlay current (walkCurrent out)
    level descriptor va meaning currentDisCH
  have nativeBound : (S1LogicalReference.outputAddress va level (walkCurrent out).baseaddress
      ((walkCurrent out).contiguous == 1#1)).address.toNat < 2 ^ (effectiveBits spec.physicalConfig).toNat := by
    rw [output]; exact outputBound
  have nativeNT : (walkCurrent out).level < 3 → blockFaultValue state.regs descriptor = false := by
    intro small
    apply noNT
    have levelEq := meaning.level_eq
    omega
  rcases out with ⟨alignedOut, slotOut, descriptorOut, kindOut, faultOut, a64Out, s2Out,
    sklOut, addressOut, next⟩
  simp only [walkDescriptor] at descriptorEq
  subst descriptor
  have kindEq : kindOut = .DescriptorType_Leaf := by
    cases kindOut <;> cases stop <;> rfl
  subst kindOut
  obtain ⟨other, suffixCall, registers, memory, events⟩ :=
    suffix_no_fault_total spec.params spec.physicalConfig va acc context entry alignedOut slotOut descriptorOut
      faultOut a64Out s2Out sklOut addressOut next level state format.d128 format.tg format.ips
      physical cache positive valid meaning.level_eq meaning.nonsecure noFault afReady nativeNT nativeBound
  refine ⟨other, suffixCall, ?_, registers, memory, events⟩
  simpa only [WalkLeafEndpoint, memory] using endpointSaved

#print axioms endpoint_suffix_total
end ArmCertWalk
