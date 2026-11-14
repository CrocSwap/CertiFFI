-- (H-P13 (3),): fetched-state premises of the shim's two data accesses, STP X9, X30, [SP]
-- (s3) and LDP X9, X30, [SP] (s7), the 16-byte slot at SP = the body's SP pin p.sp, over consumerMapShim's
-- frame disjunct. Same shape as Memory's C3Pair.prem_Stp / prem_Ldp, so Memory's mem_tailD_Stp/Ldp apply.
import HeapV2StepCerts.C3Pair
import Bridge.CruxGenGuarded.ConsumerMapShim
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxRecDepth 4096
namespace RtShim.SlotPrem
open ArmCertWalk ArmBridge.Draft HeapV2StepCerts.C3

/-- Deployment facts of the shim slot (mapped below 2^56, not MMIO, outside the table footprint). -/
def ShimSlotStatic (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (fp : Footprint) : Prop :=
  ∃ pa : BitVec 56, DataFacts mapping fp (BitVec.ofNat 64 p.sp) 16 pa

/-- The slot's bytes are present at a state. -/
def ShimSlotPresent (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (s : NativeState) : Prop :=
  ∀ n, mapping (BitVec.ofNat 64 p.sp) = some n → ∀ i < 16, (s.mem[n + i]?).isSome

theorem access_of_closed_shim {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {S : Nat × Nat × Int × Nat × Bool → Prop} {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    {s : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMapShim S p base mapping table) s)
    {va : BitVec 64} (hva : va = BitVec.ofNat 64 p.sp) {w : Bool} {acc : AccessDescriptor} (shape : DataShape w acc) :
    domain ⟨va, ⟨acc, true⟩, 16⟩ ∧
      ∃ data : S1AccessData spec config rows ⟨va, ⟨acc, true⟩, 16⟩,
        CurrentS1AccessAt spec config rows mapping ⟨va, ⟨acc, true⟩, 16⟩ data s := by
  have permitted : HeapV2E17.PermittedShim S p base va acc 16 := Or.inr (Or.inr ⟨w, hva, rfl, shape⟩)
  obtain ⟨⟨va', ⟨raw, aligned⟩, size⟩, hva', hraw, haligned, hsize, inDomain, data, current⟩ :=
    closed va acc true _ permitted
  simp only at hva' hraw haligned hsize
  subst hva' hraw haligned hsize
  exact ⟨inDomain, data, current⟩

theorem shim_addr (fetched : NativeState) : ArmCertMem.LdpEval.ldpAddr fetched (0#7) = fetched.regs.SP_EL0 := by
  simp [ArmCertMem.LdpEval.ldpAddr]

/-- s3: STP X9, X30, [SP] at SP = p.sp. -/
theorem prem_shimStp {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {S : Nat × Nat × Int × Nat × Bool → Prop} {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (fetched : NativeState)
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMapShim S p base mapping table) fetched)
    (static : ShimSlotStatic p mapping (rowsFootprint spec.imageRows)) (post : MemM1.MemReadD2.PostRegs2 fetched.regs)
    (spAt : fetched.regs.SP_EL0 = BitVec.ofNat 64 p.sp) (spAligned : (BitVec.ofNat 64 p.sp).toNat % 16 = 0) :
    (∀ acc, DataShape true acc → domain (MemClass.Stp.query fetched (0#7) acc) ∧
      (∃ data : S1AccessData spec config rows (MemClass.Stp.query fetched (0#7) acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Stp.query fetched (0#7) acc) data fetched) ∧
      MemM1.MemWriteD6.PreW acc fetched.regs) ∧
    fetched.regs.SP_EL0.toNat % 16 = 0 ∧ (ArmCertMem.LdpEval.ldpAddr fetched (0#7)).toNat % 16 = 0 ∧
    ∃ pa : BitVec 56, mapping (ArmCertMem.LdpEval.ldpAddr fetched (0#7)) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
      ∀ i < 16, ¬ (rowsFootprint spec.imageRows).byte (pa.toNat + i) := by
  have hva : ArmCertMem.LdpEval.ldpAddr fetched (0#7) = BitVec.ofNat 64 p.sp := (shim_addr fetched).trans spAt
  obtain ⟨pa, facts⟩ := static
  refine ⟨fun acc shape => ?_, by rw [spAt]; exact spAligned, by rw [hva]; exact spAligned, pa,
    by rw [hva]; exact facts.mapped, facts.mmio, fun i hi => facts.outside i hi⟩
  have r := access_of_closed_shim closed hva shape
  exact ⟨r.1, r.2, preW_of_post2 post acc⟩

/-- s7: LDP X9, X30, [SP] at SP = p.sp, with the slot bytes present. -/
theorem prem_shimLdp {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {S : Nat × Nat × Int × Nat × Bool → Prop} {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (fetched : NativeState)
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMapShim S p base mapping table) fetched)
    (static : ShimSlotStatic p mapping (rowsFootprint spec.imageRows)) (present : ShimSlotPresent p mapping fetched)
    (spAt : fetched.regs.SP_EL0 = BitVec.ofNat 64 p.sp) (spAligned : (BitVec.ofNat 64 p.sp).toNat % 16 = 0) :
    (∀ acc, DataShape false acc → domain (MemClass.Ldp.query fetched (0#7) acc) ∧
      ∃ data : S1AccessData spec config rows (MemClass.Ldp.query fetched (0#7) acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Ldp.query fetched (0#7) acc) data fetched) ∧
    fetched.regs.SP_EL0.toNat % 16 = 0 ∧ (ArmCertMem.LdpEval.ldpAddr fetched (0#7)).toNat % 16 = 0 ∧
    ∃ pa : BitVec 56, mapping (ArmCertMem.LdpEval.ldpAddr fetched (0#7)) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
      ∃ data : BitVec 128, ∀ i < 16, fetched.mem[pa.toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * i) 8) := by
  have hva : ArmCertMem.LdpEval.ldpAddr fetched (0#7) = BitVec.ofNat 64 p.sp := (shim_addr fetched).trans spAt
  obtain ⟨pa, facts⟩ := static
  obtain ⟨v, hv⟩ := exists_value (fun i => fetched.mem[pa.toNat + i]?) 16
    (fun i hi => present pa.toNat facts.mapped i hi)
  refine ⟨fun acc shape => access_of_closed_shim closed hva shape, by rw [spAt]; exact spAligned,
    by rw [hva]; exact spAligned, pa, by rw [hva]; exact facts.mapped, facts.mmio, v, hv⟩

#print axioms access_of_closed_shim
#print axioms prem_shimStp
#print axioms prem_shimLdp
end RtShim.SlotPrem
