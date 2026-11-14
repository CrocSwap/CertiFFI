-- Memory (certiffi (c3)): fetched-state premises of the byte memory classes (Ldrb/Strb, post-index,
-- base X[Rn]) from RegBind + closed membership + DataStatic + DataPresent.
import HeapV2StepCerts.C3Core
import HeapV2StepCerts.MemHolds
import MemM1.MemWriteD6
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxRecDepth 4096
namespace HeapV2StepCerts.C3
open ArmCertWalk ArmBridge.Draft HeapV2StepCerts.RegBind

theorem base_va {p : HeapV2E17.Pins} {s : NativeState} {e : Nat × Nat × Int × Nat × Bool}
    (member : e ∈ HeapV2Plan.symbolicAccesses) (bound : RegBind p e.1 s) {Rn : BitVec 5}
    (hat : accessAt e.1 = some (.x (rk Rn), 0)) :
    s.regs.gpr[(GPRSummary.key Rn.toNat).val] = HeapV2E17.dataVA p e := by
  have h := va_of_bind member bound hat
  have z : BitVec.ofInt 64 0 = 0#64 := rfl
  simpa only [regVal, rk, z, BitVec.add_zero] using h

/-- PreW for every descriptor, from the memory configuration (TagOK via no MTE2). -/
theorem preW_of_post2 {r : Regs} (post : MemM1.MemReadD2.PostRegs2 r) (acc : AccessDescriptor) :
    MemM1.MemWriteD6.PreW acc r :=
  ⟨post.post.el0, post.post.nrw, post.post.noRME, post.post.vhe, post.post.aa64el0, post.post.ns,
    post.post.e2h, post.post.tge, post.post.e0e, Or.inr post.noMTE2⟩

theorem prem_Ldrb {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop} (fetched : NativeState)
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMap p base mapping table) fetched)
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (present : DataPresent p mapping fetched)
    {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (bound : RegBind p e.1 fetched)
    (Rn : BitVec 5) (hat : accessAt e.1 = some (.x (rk Rn), 0)) (hsize : e.2.2.2.1 = 1) (hw : e.2.2.2.2 = false) :
    (∀ acc, DataShape false acc → domain (MemClass.Ldrb.query fetched Rn acc) ∧
      ∃ data : S1AccessData spec config rows (MemClass.Ldrb.query fetched Rn acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Ldrb.query fetched Rn acc) data fetched) ∧
    ∃ pa : BitVec 56, mapping (MemClass.Ldrb.base fetched Rn) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
      ¬ (rowsFootprint spec.imageRows).byte pa.toNat ∧ ∃ v : BitVec 8, fetched.mem[pa.toNat]? = some v := by
  have hva : MemClass.Ldrb.base fetched Rn = HeapV2E17.dataVA p e := base_va member bound hat
  obtain ⟨pa, facts⟩ := data_facts static member
  refine ⟨fun acc shape => ?_, pa, by rw [hva]; exact facts.mapped, facts.mmio,
    by have := facts.outside 0 (by omega); simpa using this, ?_⟩
  · have r := access_of_closed closed member hva (hw ▸ shape)
    rw [hsize] at r
    exact r
  · have hs := present e member pa.toNat facts.mapped 0 (by omega)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
    exact ⟨v, by simpa using hv⟩

theorem prem_Strb {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop} (fetched : NativeState)
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMap p base mapping table) fetched)
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (post : MemM1.MemReadD2.PostRegs2 fetched.regs)
    {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (bound : RegBind p e.1 fetched)
    (Rn : BitVec 5) (hat : accessAt e.1 = some (.x (rk Rn), 0)) (hsize : e.2.2.2.1 = 1) (hw : e.2.2.2.2 = true) :
    (∀ acc, DataShape true acc → domain (MemClass.Strb.query fetched Rn acc) ∧
      (∃ data : S1AccessData spec config rows (MemClass.Strb.query fetched Rn acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Strb.query fetched Rn acc) data fetched) ∧
      MemM1.MemWriteD6.PreW acc fetched.regs) ∧
    ∃ pa : BitVec 56, mapping (MemClass.Strb.base fetched Rn) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
      ¬ (rowsFootprint spec.imageRows).byte pa.toNat := by
  have hva : MemClass.Strb.base fetched Rn = HeapV2E17.dataVA p e := base_va member bound hat
  obtain ⟨pa, facts⟩ := data_facts static member
  refine ⟨fun acc shape => ?_, pa, by rw [hva]; exact facts.mapped, facts.mmio,
    by have := facts.outside 0 (by omega); simpa using this⟩
  have r := access_of_closed closed member hva (hw ▸ shape)
  rw [hsize] at r
  exact ⟨r.1, r.2, preW_of_post2 post acc⟩

#print axioms prem_Ldrb
#print axioms prem_Strb
end HeapV2StepCerts.C3
