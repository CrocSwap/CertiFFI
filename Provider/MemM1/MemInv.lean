import MemM1.StepRun2
import MemM1.ConsumerB
import M1a.Block2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.MemInv
abbrev State := SequentialState Regs oracleChoiceSource
open S1OuterSetup S1LogicalReference ArmCert.Eval.M1a ArmCert.Eval.M1a.TWP ArmCert.Eval.M1a.WEv
open ArmCert.Eval.M1a.TB (Host20T)
open ArmCert.Eval.M1a.B2 (WalkFactE2 translate_walk_path_evT2)
open ArmCert.Premises.TranslationAgreesV3
open ArmBridge.BoundaryV2 (UnmappedSame MappedPA MapOK)
open MemM1.WalkKE (walkK descOf)
open MemM1.WalkK2 (walkK2)
open MemM1.ConsumerV2 (Page)
open MemM1.ConsumerB (kmapB walkB)
open MemM1.StepInv2 (SysEq2 PathIn WalkByte slot1 slot2 rootSlot_eq rootOf_eq descOf_congr
  pathIn_step walkFactE_of_pathIn agrees_walk_congr walkK_congr)

/-! Memory's run invariant for the page + block consumer map `kmapB P4 P2` with the walk fixed at
the run's start state `s0` (`walkB s0.regs s0.mem P2`), in eval's heap-lift v2 interface. -/

/-! ### Level-2 (block) analogue of the StepInv2 machinery -/

/-- The block walk reads the descriptors at the root and level-1 slots (16 bytes). -/
def WalkByte2 (r : Regs) (mem : S1ResourcePath.Memory) (va : BitVec 64) (a : Nat) : Prop :=
  ∃ i < 8, a = (rootSlot r va).address.toNat + i ∨ a = (slot1 r mem va).address.toNat + i

theorem walkK2_eq (r : Regs) (mem : S1ResourcePath.Memory) (va : BitVec 64) :
    walkK2 r mem va = [(rootSlot r va).address.toNat, (slot1 r mem va).address.toNat,
      (slot2 r mem va).address.toNat] := rfl

theorem slots2_congr (r r' : Regs) (mem mem' : S1ResourcePath.Memory) (va : BitVec 64)
    (hroot : rootSlot r' va = rootSlot r va)
    (hmem : ∀ a, WalkByte2 r mem va a → mem'[a]? = mem[a]?) :
    slot1 r' mem' va = slot1 r mem va ∧ slot2 r' mem' va = slot2 r mem va := by
  have e1 : slot1 r' mem' va = slot1 r mem va := by
    unfold slot1
    rw [hroot, descOf_congr mem mem' _ (fun i hi => hmem _ ⟨i, hi, Or.inl rfl⟩)]
  refine ⟨e1, ?_⟩
  unfold slot2
  rw [e1, descOf_congr mem mem' _ (fun i hi => hmem _ ⟨i, hi, Or.inr rfl⟩)]

theorem walkK2_congr (r r' : Regs) (mem mem' : S1ResourcePath.Memory) (va : BitVec 64)
    (hroot : rootSlot r' va = rootSlot r va)
    (hmem : ∀ a, WalkByte2 r mem va a → mem'[a]? = mem[a]?) :
    walkK2 r' mem' va = walkK2 r mem va := by
  rcases slots2_congr r r' mem mem' va hroot hmem with ⟨e1, e2⟩
  rw [walkK2_eq, walkK2_eq, hroot, e1, e2]

theorem walkByte2_congr (r r' : Regs) (mem mem' : S1ResourcePath.Memory) (va : BitVec 64)
    (hroot : rootSlot r' va = rootSlot r va)
    (hmem : ∀ a, WalkByte2 r mem va a → mem'[a]? = mem[a]?) (a : Nat) :
    WalkByte2 r' mem' va a ↔ WalkByte2 r mem va a := by
  rcases slots2_congr r r' mem mem' va hroot hmem with ⟨e1, _⟩
  unfold WalkByte2
  rw [hroot, e1]

/-- eval's `translate_walk_path_evT2` inputs (path to a level-2 leaf) other than Host20T and EPD0,
    plus coverage of the table bytes `TB`: observed descriptors, the leaf, and the walk bytes. -/
def PathIn2 (s : State) (va D : BitVec 64) (TB : Nat → Prop) : Prop :=
  ∃ (observe : Observation) (slotL : Nat) (physL : FullAddress) (vL : S1DescriptorPIE.View 64),
    Available observe (fun p => S2TableRAM.OrdinaryRAM p.address) ∧
    Realizes observe false false true true (fun a => s.mem[a]?) ∧
    S1EntryPathSlots.Identity observe ∧
    (∀ l p v d, observe l p v → BytesAt false (fun a => s.mem[a]?) p d →
      ∀ level : Nat, descriptorKind level v.stable = .ok .table → TablePermsZero d) ∧
    Path observe 48 va 0 9 ((rootOf s.regs va).setWidth 48) (.leaf 2 slotL physL vL) ∧
    BytesAt false (fun a => s.mem[a]?) physL D ∧
    (S1Contiguous.bit D = 0#1 ∧ BitVec.join1 [BitVec.access D 10] = 1#1 ∧
      BitVec.join1 [BitVec.access D 16] = 0#1 ∧
      ∀ v : TTWState, v.level = 2 → v.baseaddress.address = S1LeafBaseFrame.base D 2 →
        (!is_zero_subrange (S1StageOA.address va v).address 55 48) = false) ∧
    (!is_zero_subrange (rootSlot s.regs va).address 55 48) = false ∧
    Covers observe TB ∧ (∀ i < 8, TB (physL.address.toNat + i)) ∧
    (∀ a, WalkByte2 s.regs s.mem va a → TB a)

theorem pathIn2_step (s s' : State) (va D : BitVec 64) (TB : Nat → Prop)
    (hsys : SysEq2 s.regs s'.regs) (hmem : ∀ a, TB a → s'.mem[a]? = s.mem[a]?)
    (h : PathIn2 s va D TB) : PathIn2 s' va D TB := by
  rcases h with ⟨observe, slotL, physL, vL, hav, hre, hid, htab, hpath, hD, hleaf, hroot, hcov, hphys, hwb⟩
  have hb : ∀ p : FullAddress, (∀ i < 8, TB (p.address.toNat + i)) → ∀ d,
      (BytesAt false (fun a => s'.mem[a]?) p d ↔ BytesAt false (fun a => s.mem[a]?) p d) := by
    intro p hp d
    constructor
    · intro hb' i hi; exact (hmem _ (hp i hi)).symm.trans (hb' i hi)
    · intro hb' i hi; exact (hmem _ (hp i hi)).trans (hb' i hi)
  have hrs := rootSlot_eq hsys va
  have hwm : ∀ a, WalkByte2 s.regs s.mem va a → s'.mem[a]? = s.mem[a]? := fun a ha => hmem a (hwb a ha)
  refine ⟨observe, slotL, physL, vL, hav, ?_, hid, ?_, ?_, ?_, hleaf, ?_, hcov, hphys, ?_⟩
  · intro l p v hobs
    rcases hre l p v hobs with ⟨d, hbd, hv⟩
    exact ⟨d, (hb p (hcov l p v hobs) d).2 hbd, hv⟩
  · intro l p v d hobs hbd
    exact htab l p v d hobs ((hb p (hcov l p v hobs) d).1 hbd)
  · rw [rootOf_eq hsys]; exact hpath
  · exact (hb physL hphys D).2 hD
  · rw [hrs]; exact hroot
  · intro a ha
    exact hwb a ((walkByte2_congr s.regs s'.regs s.mem s'.mem va hrs hwm a).1 ha)

theorem walkFactE2_of_pathIn2 (s : State) (va D : BitVec 64) (TB : Nat → Prop) (hH : Host20T s)
    (hEPD0 : _get_TCR_EL2_Type_EPD0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1)
    (hva : va.toNat < 2^48) (h : PathIn2 s va D TB) : WalkFactE2 s va D := by
  rcases h with ⟨observe, slotL, physL, vL, hav, hre, hid, htab, hpath, hD, hleaf, hroot, _, _, _⟩
  exact translate_walk_path_evT2 s hH va (MemM1.VA.varange va hva) hEPD0 hroot observe hav hre hid htab
    slotL physL vL hpath D hD hleaf

/-! ### Inputs at s0 and the invariant -/

/-- **The instance inputs at the run's start state `s0`** for `kmapB P4 P2` with table bytes `TB`. -/
structure MemInputs (s0 : State) (P4 P2 : BitVec 64 → Option Page) (TB : Nat → Prop) : Prop where
  regs20 : MemM1.Witness.Regs20 s0.regs
  sctlrC : _get_SCTLR_EL2_Type_C (s0.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1
  sctlrI : _get_SCTLR_EL2_Type_I (s0.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1
  host : Host20T s0
  epd0 : _get_TCR_EL2_Type_EPD0 (s0.regs.bank_BitVec_64 .TCR_EL2) = 0#1
  pages : ∀ (va : BitVec 64) (p : Page), va.toNat < 2^48 → P2 (va >>> 21) = none →
    P4 (va >>> 12) = some p →
    PathIn s0 va p.leaf TB ∧
      (if p.code then MemM1.WalkFactV.LeafBitsC p.leaf else MemM1.ConsumerD.LeafBitsD p.leaf)
  blocks : ∀ (va : BitVec 64) (b : Page), va.toNat < 2^48 → P2 (va >>> 21) = some b →
    PathIn2 s0 va b.leaf TB ∧
      (if b.code then MemM1.WalkFactV.LeafBitsC b.leaf else MemM1.ConsumerD.LeafBitsD b.leaf)
  tbUnmapped : ∀ a, TB a → ¬ MappedPA (kmapB P4 P2) a
  mapOK : MapOK (kmapB P4 P2)
  pins : DataPins s0

/-- **Memory's run invariant**: the start-state inputs, the system registers unchanged
    (`SysEq2`), and unmapped RAM unchanged since `s0`. -/
def MemInv (s0 : State) (P4 P2 : BitVec 64 → Option Page) (TB : Nat → Prop) (s : State) : Prop :=
  MemInputs s0 P4 P2 TB ∧ SysEq2 s0.regs s.regs ∧ UnmappedSame (kmapB P4 P2) s0 s

theorem memInv_refl (s0 : State) (P4 P2 : BitVec 64 → Option Page) (TB : Nat → Prop)
    (h : MemInputs s0 P4 P2 TB) : MemInv s0 P4 P2 TB s0 :=
  ⟨h, SysEq2.refl _, UnmappedSame.refl _ _⟩

theorem memInv_step (s0 : State) (P4 P2 : BitVec 64 → Option Page) (TB : Nat → Prop) (s s' : State)
    (h : MemInv s0 P4 P2 TB s) (hsys : SysEq2 s.regs s'.regs) (hU : UnmappedSame (kmapB P4 P2) s s') :
    MemInv s0 P4 P2 TB s' :=
  ⟨h.1, h.2.1.trans hsys, h.2.2.trans hU⟩

/-- **E17 v3 at a later state for `kmapB`, walk fixed at `s0`.** -/
theorem agreesV3_step_B (s0 s : State) (P4 P2 : BitVec 64 → Option Page) (TB : Nat → Prop)
    (hI : MemInputs s0 P4 P2 TB) (hsys : SysEq2 s0.regs s.regs)
    (hmem : ∀ a, TB a → s.mem[a]? = s0.mem[a]?) :
    TranslationAgrees (kmapB P4 P2) (walkB s0.regs s0.mem P2) s := by
  have hR' := MemM1.StepInv2.regs20 hsys hI.regs20
  have hC' : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1 := by rw [hsys.sctlr]; exact hI.sctlrC
  have hI' : _get_SCTLR_EL2_Type_I (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1 := by rw [hsys.sctlr]; exact hI.sctlrI
  have hH' := MemM1.StepInv2.host20T hsys hI.host
  have hE' : _get_TCR_EL2_Type_EPD0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1 := by rw [hsys.tcr]; exact hI.epd0
  have hA := MemM1.ConsumerB.agreesV3_kmapB_full s hR' hC' hI' P4 P2
    (fun va p hva h2 h4 =>
      ⟨walkFactE_of_pathIn s va p.leaf TB hH' hE' hva
        (pathIn_step s0 s va p.leaf TB hsys hmem (hI.pages va p hva h2 h4).1), (hI.pages va p hva h2 h4).2⟩)
    (fun va b hva h2 =>
      ⟨walkFactE2_of_pathIn2 s va b.leaf TB hH' hE' hva
        (pathIn2_step s0 s va b.leaf TB hsys hmem (hI.blocks va b hva h2).1), (hI.blocks va b hva h2).2⟩)
  refine agrees_walk_congr _ _ _ s hA ?_
  intro va acc al sz hp
  rcases hp with ⟨hva, _, hrest⟩
  have hrs := rootSlot_eq hsys va
  rcases hrest with ⟨b, h2, _, _⟩ | ⟨h2, _, p, h4, _⟩
  · simp only [walkB, h2]
    rcases (hI.blocks va b hva h2).1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hwb⟩
    exact walkK2_congr s0.regs s.regs s0.mem s.mem va hrs (fun a ha => hmem a (hwb a ha))
  · simp only [walkB, h2]
    rcases (hI.pages va p hva h2 h4).1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hwb⟩
    exact walkK_congr s0.regs s.regs s0.mem s.mem va hrs (fun a ha => hmem a (hwb a ha))

theorem dataPins_step {s s' : State} (hsys : SysEq2 s.regs s'.regs) (h : DataPins s) : DataPins s' :=
  ⟨by rw [hsys.spe]; exact h.spe, by rw [hsys.sctlr]; exact h.e0e, by rw [hsys.feat]; exact h.mte2Off,
    by rw [hsys.feat]; exact h.lse2, by rw [hsys.feat]; exact h.tmeOff⟩

/-- **What the invariant gives at every run state**: E17 v3 for `kmapB P4 P2` with the walk fixed
    at `s0`, MapOK, and the data pins. -/
theorem memInv_agrees (s0 : State) (P4 P2 : BitVec 64 → Option Page) (TB : Nat → Prop) (s : State)
    (h : MemInv s0 P4 P2 TB s) :
    TranslationAgrees (kmapB P4 P2) (walkB s0.regs s0.mem P2) s ∧ MapOK (kmapB P4 P2) ∧ DataPins s := by
  rcases h with ⟨hI, hsys, hU⟩
  refine ⟨agreesV3_step_B s0 s P4 P2 TB hI hsys (fun a ha => hU a (hI.tbUnmapped a ha) id), hI.mapOK,
    dataPins_step hsys hI.pins⟩

#print axioms walkK2_congr
#print axioms pathIn2_step
#print axioms walkFactE2_of_pathIn2
#print axioms memInv_refl
#print axioms memInv_step
#print axioms agreesV3_step_B
#print axioms dataPins_step
#print axioms memInv_agrees
end MemM1.MemInv
