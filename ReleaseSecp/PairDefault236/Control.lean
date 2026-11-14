import PairDefault236.Current
import NativeAccess.PairGeometry
import NativeAccess.Plans
import NativeAccess.StoreLoops
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open TagCheckFrames
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option Elab.async false
namespace PairDefault236.Control
open NativeMteTagCheck NativeMteTagCheck.StatusTrace

theorem unaligned_preserves (acc : AccessDescriptor) (a : BitVec 64) (size : Int) :
    Preserves (AArch64_UnalignedAccessFaults acc a size) := by oracle_frame

theorem readPrefix_preserves (a : BitVec 64) (N : Nat) (acc : AccessDescriptor) :
    Preserves (NativeAccess.Plans.readPrefix a N acc) := by oracle_frame

theorem storePrefix_preserves (a : BitVec 64) (N : Nat) (acc : AccessDescriptor) (value : BitVec (N * 8)) :
    Preserves (NativeAccess.StoreLoops.storePrefix a N acc value) := by oracle_frame

theorem devpage_preserves : Preserves (ConstrainUnpredictable .Unpredictable_DEVPAGE2) := by oracle_frame

#print axioms unaligned_preserves
#print axioms readPrefix_preserves
#print axioms storePrefix_preserves
#print axioms devpage_preserves


theorem create_gpr_preserves (op : MemOp) (nt up tc : Bool) :
    Preserves (CreateAccDescGPR op nt up tc) := by oracle_frame

theorem natural_of_fit (a : BitVec 64) (fit : NativeMte2.Read.Within16 a 16) : a.toNat % 16 = 0 := by
  by_cases h : a.toNat % 16 = 0
  · exact h
  have bad := NativeAccess.PairGeometry.join_false_of_mod16 a h
  change NativeAccess.PairGeometry.joinTest a = true at fit
  rw [fit] at bad
  cases bad

-- Supplemental trace bridges retain independent execution-derived oracle facts.
open S1Normality

theorem occ_normal (site : Nat) (s : State) (different : site ≠ 1354 := by decide) :
    ∃ label t, (occLabel site : SailM ChoiceLabel) s = .ok label t ∧ TraceFrame s t :=
  NativeMteTagCheck.StatusTrace.occ_trace site s different

theorem bits_normal (width : Nat) (label : ChoiceLabel) (s : State) :
    ∃ bits t, undefined_bitvector_at label width s = .ok bits t ∧ TraceFrame s t :=
  NativeMteTagCheck.StatusTrace.bits_trace width label s

theorem bool_normal (label : ChoiceLabel) (s : State) :
    ∃ value t, undefined_bool_at label () s = .ok value t ∧ TraceFrame s t := by
  obtain ⟨value,t,run,f⟩ := S1EntryCalleesExtra.bool_normal label s
  exact ⟨value,t,run,f.1,f.2.1,f.2.2,TagCheckFrames.bool_preserves label s value t run⟩

theorem constraint_normal (label : ChoiceLabel) (s : State) :
    ∃ value t, undefined_Constraint label () s = .ok value t ∧ TraceFrame s t := by
  obtain ⟨value,t,run,f⟩ := MemM1.MemWriteD3.constraint_normal label s
  exact ⟨value,t,run,f.1,f.2.1,f.2.2,TagCheckFrames.constraint_preserves label s value t run⟩

theorem plain_unaligned_allowed (s : State) (g : NativeAccess.HostPins s)
    (a : _get_SCTLR_EL2_Type_A (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1)
    (acc : AccessDescriptor) (p : NativeAccess.Plain acc) (address : BitVec 64) (size : Int) :
    ∃ u, (AArch64_UnalignedAccessFaults acc address size : SailM Bool) s = .ok false u ∧ TraceFrame s u := by
  obtain ⟨u,run,r,m,e⟩ := NativeAccess.plain_unaligned_allowed s g a acc p address size
  exact ⟨u,run,r,m,e,unaligned_preserves acc address size s false u run⟩

theorem be_false (s : State)
    (hEL : s.regs.PSTATE.EL = 0#2) (hnRW : s.regs.PSTATE.nRW = 0#1)
    (hR : s.regs.FeatureImpl[232] = false) (hVHE : s.regs.FeatureImpl[54] = true)
    (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (hE2H : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 34 34 = 1#1)
    (hTGE : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 27 27 = 1#1)
    (hE0E : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCTLR_EL2) 24 24 = 0#1) :
    ∃ t, BigEndian .AccessType_GPR s = .ok false t ∧ TraceFrame s t := by
  obtain ⟨t,run,f⟩ := MemM1.MemReadDBE.be_false s hEL hnRW hR hVHE hAA hNS hE2H hTGE hE0E
  exact ⟨t,run,f.1,f.2.1,f.2.2,TagCheckFrames.bigEndian_preserves .AccessType_GPR s false t run⟩

open MemM1.MemReadD MemM1.MemWriteD5
theorem littleEndian_of (acc : AccessDescriptor) (hA : AccDWT acc) {s : State} (post : PostRegs s.regs) :
    ∀ u, TraceFrame s u → ∃ t, BigEndian acc.acctype u = .ok false t ∧ TraceFrame u t := by
  intro u fu
  rw [hA.base.gpr]
  exact be_false u (by rw [fu.1]; exact post.el0) (by rw [fu.1]; exact post.nrw)
    (by rw [fu.1]; exact post.noRME) (by rw [fu.1]; exact post.vhe) (by rw [fu.1]; exact post.aa64el0)
    (by rw [fu.1]; exact post.ns) (by rw [fu.1]; exact post.e2h) (by rw [fu.1]; exact post.tge)
    (by rw [fu.1]; exact post.e0e)

#print axioms plain_unaligned_allowed
#print axioms littleEndian_of
end PairDefault236.Control
