import MemM1.ConsumerV3F
import M1a.TcrBits
import M1a.Fetch
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.StepInv2
abbrev State := SequentialState Regs oracleChoiceSource
open S1OuterSetup S1LogicalReference ArmCert.Eval.M1a ArmCert.Eval.M1a.TWP ArmCert.Eval.M1a.WEv
open ArmCert.Eval.M1a.TB (Host20T HostT TcrBits translate_walk_path_evT)
open ArmCert.Premises.TranslationAgreesV3
open MemM1.WalkKE (walkK descOf)
open MemM1.ConsumerV2 (Page kmap)

/-! Step invariance of the E17 v3 kmap instance: `walkK` and the per-page walk inputs depend only
on a fixed list of system registers (`SysEq`) and on the translation-table bytes; GPR/SP/PC/NZCV
writes and stores outside the table bytes preserve them, so the run's walk function
`walkK s.regs s.mem` stays valid at later states. -/

/-! ### 1. System-register agreement -/

/-- `StepInv.SysEq` with EDSCR restricted to the one bit read (HDE, bit 14: Regs20.hde and
 CheckDebug's halting test); per-step EDSCR.PipeAdv/bits 30:29 update preserves it.
    None of the step bookkeeping registers (SEE, ShouldAdvanceIT/SS, BTypeCompatible,
    __InstructionStep, InGuardedPage, BTypeNext, PSTATE.BTYPE, __BranchTaken, MDCCSR_EL0) is listed.
    The register fields read by Regs20, Host20T (HostT, TcrBits), rootOf/rootSlot, EPD0,
    SCTLR_EL2.C/I, DataPins and BEPins. -/
structure SysEq2 (r r' : Regs) : Prop where
  feat : r'.FeatureImpl = r.FeatureImpl
  el : r'.PSTATE.EL = r.PSTATE.EL
  nrw : r'.PSTATE.nRW = r.PSTATE.nRW
  sctlr : r'.bank_BitVec_64 .SCTLR_EL2 = r.bank_BitVec_64 .SCTLR_EL2
  tcr : r'.bank_BitVec_64 .TCR_EL2 = r.bank_BitVec_64 .TCR_EL2
  tcr2 : r'.bank_BitVec_64 .TCR2_EL2 = r.bank_BitVec_64 .TCR2_EL2
  hcr : r'.bank_BitVec_64 .HCR_EL2 = r.bank_BitVec_64 .HCR_EL2
  scr : r'.bank_BitVec_64 .SCR_EL3 = r.bank_BitVec_64 .SCR_EL3
  mair : r'.bank_BitVec_64 .MAIR_EL2 = r.bank_BitVec_64 .MAIR_EL2
  mdscr : r'.bank_BitVec_64 .MDSCR_EL1 = r.bank_BitVec_64 .MDSCR_EL1
  httbr : r'.bank_BitVec_64 .HTTBR = r.bank_BitVec_64 .HTTBR
  ttbr0 : r'.bank_BitVec_128 ._TTBR0_EL2 = r.bank_BitVec_128 ._TTBR0_EL2
  ttbr1 : r'.bank_BitVec_128 .TTBR1_EL2 = r.bank_BitVec_128 .TTBR1_EL2
  hde : _get_EDSCR_Type_HDE (r'.bank_BitVec_32 ._EDSCR) = _get_EDSCR_Type_HDE (r.bank_BitVec_32 ._EDSCR)
  tlb : r'.bank_Bool .__tlb_enabled = r.bank_Bool .__tlb_enabled
  spe : r'.bank_Bool .SPESampleInFlight = r.bank_Bool .SPESampleInFlight
  pa : r'.bank_Int .__supported_pa_size = r.bank_Int .__supported_pa_size

theorem SysEq2.refl (r : Regs) : SysEq2 r r :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SysEq2.trans {r r' r'' : Regs} (h : SysEq2 r r') (h' : SysEq2 r' r'') : SysEq2 r r'' :=
  ⟨h'.feat.trans h.feat, h'.el.trans h.el, h'.nrw.trans h.nrw, h'.sctlr.trans h.sctlr,
    h'.tcr.trans h.tcr, h'.tcr2.trans h.tcr2, h'.hcr.trans h.hcr, h'.scr.trans h.scr,
    h'.mair.trans h.mair, h'.mdscr.trans h.mdscr, h'.httbr.trans h.httbr, h'.ttbr0.trans h.ttbr0,
    h'.ttbr1.trans h.ttbr1, h'.hde.trans h.hde, h'.tlb.trans h.tlb, h'.spe.trans h.spe,
    h'.pa.trans h.pa⟩

/-! ### 3. What native steps change keeps SysEq -/
theorem SysEq_of_gpr (r : Regs) (g) : SysEq2 r { r with gpr := g } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem SysEq_of_pc (r : Regs) (pc : BitVec 64) : SysEq2 r { r with _PC := pc } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem SysEq_of_sp (r : Regs) (sp : BitVec 64) : SysEq2 r { r with SP_EL0 := sp } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem SysEq_of_nzcv (r : Regs) (n z c v : BitVec 1) :
    SysEq2 r { r with PSTATE := { r.PSTATE with N := n, Z := z, C := c, V := v } } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem SysEq_of_z (r : Regs) (zr) : SysEq2 r { r with _Z := zr } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Native-1 per-step bookkeeping keeps SysEq2 -/

/-- Verbatim copy of `Bridge.CruxX.preFetchRegs` (that package is not on this leanpath). -/
def preFetchRegs (r : Regs) : Regs :=
  { r with
    bank_Int := (r.bank_Int.set .SEE (-1))
    ShouldAdvanceSS := true
    ShouldAdvanceIT := false
    bank_BitVec_32 := (r.bank_BitVec_32.set ._EDSCR
      (_update_EDSCR_Type_PipeAdv (Sail.BitVec.updateSubrange (r.bank_BitVec_32 ._EDSCR) 30 29
        (Sail.BitVec.slice (r.bank_BitVec_64 .MDCCSR_EL0) 29 2)) 1#1))
    bank_BitVec_64 := (r.bank_BitVec_64.set .MDCCSR_EL0
      (Sail.BitVec.updateSubrange (r.bank_BitVec_64 .MDCCSR_EL0) 30 29
        (Sail.BitVec.slice (_update_EDSCR_Type_PipeAdv (Sail.BitVec.updateSubrange (r.bank_BitVec_32 ._EDSCR) 30 29
          (Sail.BitVec.slice (r.bank_BitVec_64 .MDCCSR_EL0) 29 2)) 1#1) 29 2))) }

/-- The PipeAdv (bit 25) and bits 30:29 EDSCR update leaves HDE (bit 14). -/
theorem hde_pipeadv (e : BitVec 32) (x : BitVec 2) (y : BitVec 1) :
    _get_EDSCR_Type_HDE (_update_EDSCR_Type_PipeAdv (Sail.BitVec.updateSubrange e 30 29 x) y) =
      _get_EDSCR_Type_HDE e := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h0 : i = 0 := by omega
  subst h0
  simp only [_get_EDSCR_Type_HDE, _update_EDSCR_Type_PipeAdv, Sail.BitVec.extractLsb,
    BitVec.getLsbD_extractLsb, Sail.BitVec.updateSubrange]
  rw [MemM1.S1T.upd'_getLsbD _ _ _ _ _ (by decide), MemM1.S1T.upd'_getLsbD _ _ _ _ _ (by decide)]
  simp

theorem SysEq2_of_preFetch (r : Regs) : SysEq2 r (preFetchRegs r) := by
  have b64 : ∀ k : Bank_BitVec_64, k ≠ Bank_BitVec_64.MDCCSR_EL0 →
      (preFetchRegs r).bank_BitVec_64 k = r.bank_BitVec_64 k := fun k hk => by
    show RegMap.set r.bank_BitVec_64 Bank_BitVec_64.MDCCSR_EL0 _ k = _
    exact RegMap.set_ne _ _ hk
  have bint : (preFetchRegs r).bank_Int Bank_Int.__supported_pa_size = r.bank_Int Bank_Int.__supported_pa_size := by
    show RegMap.set r.bank_Int Bank_Int.SEE (-1) Bank_Int.__supported_pa_size = _
    exact RegMap.set_ne _ _ (by decide)
  have bh : _get_EDSCR_Type_HDE ((preFetchRegs r).bank_BitVec_32 ._EDSCR) =
      _get_EDSCR_Type_HDE (r.bank_BitVec_32 ._EDSCR) := by
    show _get_EDSCR_Type_HDE (RegMap.set r.bank_BitVec_32 Bank_BitVec_32._EDSCR _ Bank_BitVec_32._EDSCR) = _
    rw [RegMap.set_same]
    exact hde_pipeadv _ _ _
  exact ⟨rfl, rfl, rfl, b64 _ (by decide), b64 _ (by decide), b64 _ (by decide), b64 _ (by decide),
    b64 _ (by decide), b64 _ (by decide), b64 _ (by decide), b64 _ (by decide), rfl, rfl, bh, rfl, rfl, bint⟩

/-- Any write to a Bool-bank register other than `__tlb_enabled` / `SPESampleInFlight`
    (InGuardedPage, __InstructionStep, ...) keeps SysEq2. -/
theorem SysEq2_of_bool (r : Regs) (k : Bank_Bool) (v : Bool) (h1 : k ≠ .__tlb_enabled)
    (h2 : k ≠ .SPESampleInFlight) :
    SysEq2 r { r with bank_Bool := RegMap.set r.bank_Bool k v } := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · show RegMap.set r.bank_Bool k v Bank_Bool.__tlb_enabled = _; exact RegMap.set_ne _ _ (Ne.symm h1)
  · show RegMap.set r.bank_Bool k v Bank_Bool.SPESampleInFlight = _; exact RegMap.set_ne _ _ (Ne.symm h2)

/-- Any write to an Int-bank register other than `__supported_pa_size` (e.g. SEE) keeps SysEq2. -/
theorem SysEq2_of_int (r : Regs) (k : Bank_Int) (v : Int) (h : k ≠ .__supported_pa_size) :
    SysEq2 r { r with bank_Int := RegMap.set r.bank_Int k v } := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  show RegMap.set r.bank_Int k v Bank_Int.__supported_pa_size = _; exact RegMap.set_ne _ _ (Ne.symm h)

theorem SysEq2_of_clrGP (r : Regs) : SysEq2 r (MemM1.IF.clrGP r) :=
  SysEq2_of_bool r .InGuardedPage false (by decide) (by decide)

theorem SysEq2_of_fetchRegs (r : Regs) : SysEq2 r (ArmCert.Eval.M1a.Fetch2.fetchRegs r) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · show RegMap.set r.bank_Bool Bank_Bool.__InstructionStep false Bank_Bool.__tlb_enabled = _
    exact RegMap.set_ne _ _ (by decide)
  · show RegMap.set r.bank_Bool Bank_Bool.__InstructionStep false Bank_Bool.SPESampleInFlight = _
    exact RegMap.set_ne _ _ (by decide)

/-- Struct-field bookkeeping (ShouldAdvanceIT/SS, BTypeCompatible, BTypeNext, __BranchTaken) and
    PSTATE.BTYPE writes keep SysEq2. -/
theorem SysEq2_of_bookkeeping (r : Regs) (it ss btc : Bool) (btn : BitVec 2) (bt : Bool) (bty : BitVec 2) :
    SysEq2 r
      { r with
        ShouldAdvanceIT := it
        ShouldAdvanceSS := ss
        BTypeCompatible := btc
        BTypeNext := btn
        __BranchTaken := bt
        PSTATE := { r.PSTATE with BTYPE := bty } } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Predicate transfer -/
theorem regs20 {r r' : Regs} (h : SysEq2 r r') (hR : MemM1.Witness.Regs20 r) : MemM1.Witness.Regs20 r' := by
  rcases hR with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩
  exact ⟨by rw [h.feat]; exact a1, by rw [h.feat]; exact a2, by rw [h.feat]; exact a3,
    by rw [h.feat]; exact a4, by rw [h.feat]; exact a5, by rw [h.feat]; exact a6, by rw [h.el]; exact a7,
    by rw [h.scr]; exact a8, by rw [h.hcr]; exact a9, by rw [h.hcr]; exact a10, by rw [h.sctlr]; exact a11,
    by rw [h.mdscr]; exact a12, by rw [h.hde]; exact a13, by rw [h.spe]; exact a14⟩

theorem host20T {s s' : State} (h : SysEq2 s.regs s'.regs) (hH : Host20T s) : Host20T s' := by
  rcases hH with ⟨⟨b1, b2, b3, b4, b5, b6, b7, b8⟩, c1, c2, c3, c4, c5, c6, c7, c8⟩
  exact ⟨⟨by rw [h.feat]; exact b1, by rw [h.feat]; exact b2, by rw [h.feat]; exact b3,
      by rw [h.nrw]; exact b4, by rw [h.tcr]; exact b5, by rw [h.hcr]; exact b6, by rw [h.mair]; exact b7,
      by rw [h.feat, h.tcr2]; exact b8⟩,
    by rw [h.feat]; exact c1, by rw [h.sctlr]; exact c2, by rw [h.sctlr]; exact c3, by rw [h.pa]; exact c4,
    by rw [h.el]; exact c5, by rw [h.tlb]; exact c6, by rw [h.hcr]; exact c7, by rw [h.hcr]; exact c8⟩

theorem rootOf_eq {r r' : Regs} (h : SysEq2 r r') (va : BitVec 64) : rootOf r' va = rootOf r va := by
  have e : (Regime.Regime_EL20 == Regime.Regime_EL20) = true := rfl
  unfold rootOf S1EntryRoot.word
  simp only [e, ↓reduceIte]
  rw [h.ttbr0, h.ttbr1, h.httbr]

theorem rootSlot_eq {r r' : Regs} (h : SysEq2 r r') (va : BitVec 64) : rootSlot r' va = rootSlot r va := by
  unfold rootSlot
  rw [rootOf_eq h]

/-! ### 1. walkK congruence -/

theorem descOf_congr (mem mem' : S1ResourcePath.Memory) (a : Nat)
    (h : ∀ i < 8, mem'[a + i]? = mem[a + i]?) : descOf mem' a = descOf mem a := by
  unfold descOf
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide)]

def slot1 (r : Regs) (mem : S1ResourcePath.Memory) (va : BitVec 64) : FullAddress :=
  S1ResourcePath.nextSlot va 0 (descOf mem (rootSlot r va).address.toNat)
def slot2 (r : Regs) (mem : S1ResourcePath.Memory) (va : BitVec 64) : FullAddress :=
  S1ResourcePath.nextSlot va (0 + 1) (descOf mem (slot1 r mem va).address.toNat)

/-- **The walk bytes**: the 8 descriptor bytes at each of the first three slots (root, level 1,
    level 2), whose contents `walkK` reads to compute the next slot. -/
def WalkByte (r : Regs) (mem : S1ResourcePath.Memory) (va : BitVec 64) (a : Nat) : Prop :=
  ∃ i < 8, a = (rootSlot r va).address.toNat + i ∨ a = (slot1 r mem va).address.toNat + i ∨
    a = (slot2 r mem va).address.toNat + i

theorem walkK_eq (r : Regs) (mem : S1ResourcePath.Memory) (va : BitVec 64) :
    walkK r mem va = [(rootSlot r va).address.toNat, (slot1 r mem va).address.toNat,
      (slot2 r mem va).address.toNat,
      (S1ResourcePath.nextSlot va (0 + 1 + 1) (descOf mem (slot2 r mem va).address.toNat)).address.toNat] :=
  rfl

theorem slots_congr (r r' : Regs) (mem mem' : S1ResourcePath.Memory) (va : BitVec 64)
    (hroot : rootSlot r' va = rootSlot r va)
    (hmem : ∀ a, WalkByte r mem va a → mem'[a]? = mem[a]?) :
    slot1 r' mem' va = slot1 r mem va ∧ slot2 r' mem' va = slot2 r mem va ∧
      descOf mem' (slot2 r' mem' va).address.toNat = descOf mem (slot2 r mem va).address.toNat := by
  have e1 : slot1 r' mem' va = slot1 r mem va := by
    unfold slot1
    rw [hroot, descOf_congr mem mem' _ (fun i hi => hmem _ ⟨i, hi, Or.inl rfl⟩)]
  have e2 : slot2 r' mem' va = slot2 r mem va := by
    unfold slot2
    rw [e1, descOf_congr mem mem' _ (fun i hi => hmem _ ⟨i, hi, Or.inr (Or.inl rfl)⟩)]
  refine ⟨e1, e2, ?_⟩
  rw [e2, descOf_congr mem mem' _ (fun i hi => hmem _ ⟨i, hi, Or.inr (Or.inr rfl)⟩)]

/-- **walkK congruence**: equal root slots (TTBR0_EL2/HTTBR/TTBR1_EL2 suffice, `rootSlot_eq`) and
    agreement on the walk bytes give the same walk PA list. -/
theorem walkK_congr (r r' : Regs) (mem mem' : S1ResourcePath.Memory) (va : BitVec 64)
    (hroot : rootSlot r' va = rootSlot r va)
    (hmem : ∀ a, WalkByte r mem va a → mem'[a]? = mem[a]?) :
    walkK r' mem' va = walkK r mem va := by
  rcases slots_congr r r' mem mem' va hroot hmem with ⟨e1, e2, e3⟩
  rw [walkK_eq, walkK_eq, e3, hroot, e1, e2]

theorem walkByte_congr (r r' : Regs) (mem mem' : S1ResourcePath.Memory) (va : BitVec 64)
    (hroot : rootSlot r' va = rootSlot r va)
    (hmem : ∀ a, WalkByte r mem va a → mem'[a]? = mem[a]?) (a : Nat) :
    WalkByte r' mem' va a ↔ WalkByte r mem va a := by
  rcases slots_congr r r' mem mem' va hroot hmem with ⟨e1, e2, _⟩
  unfold WalkByte
  rw [hroot, e1, e2]

/-! ### 2. Per-page walk inputs and their transfer -/

/-- eval's `translate_walk_path_evT` inputs for `va` (other than Host20T and EPD0) at `s`, plus the
    table-byte coverage: `TB` contains every observed descriptor's 8 bytes (`Covers`), the leaf's
    8 bytes, and the walk bytes. -/
def PathIn (s : State) (va D : BitVec 64) (TB : Nat → Prop) : Prop :=
  ∃ (observe : Observation) (slotL : Nat) (physL : FullAddress) (vL : S1DescriptorPIE.View 64),
    Available observe (fun p => S2TableRAM.OrdinaryRAM p.address) ∧
    Realizes observe false false true true (fun a => s.mem[a]?) ∧
    S1EntryPathSlots.Identity observe ∧
    (∀ l p v d, observe l p v → BytesAt false (fun a => s.mem[a]?) p d →
      ∀ level : Nat, descriptorKind level v.stable = .ok .table → TablePermsZero d) ∧
    Path observe 48 va 0 9 ((rootOf s.regs va).setWidth 48) (.leaf 3 slotL physL vL) ∧
    BytesAt false (fun a => s.mem[a]?) physL D ∧
    (S1Contiguous.bit D = 0#1 ∧ BitVec.join1 [BitVec.access D 10] = 1#1 ∧
      ∀ v : TTWState, v.level = 3 → v.baseaddress.address = S1LeafBaseFrame.base D 3 →
        (!is_zero_subrange (S1StageOA.address va v).address 55 48) = false) ∧
    (!is_zero_subrange (rootSlot s.regs va).address 55 48) = false ∧
    Covers observe TB ∧ (∀ i < 8, TB (physL.address.toNat + i)) ∧
    (∀ a, WalkByte s.regs s.mem va a → TB a)

/-- **Transfer**: the per-page inputs at `s` hold at `s'` when `s'` has the same system registers
    and the same table bytes. -/
theorem pathIn_step (s s' : State) (va D : BitVec 64) (TB : Nat → Prop)
    (hsys : SysEq2 s.regs s'.regs) (hmem : ∀ a, TB a → s'.mem[a]? = s.mem[a]?)
    (h : PathIn s va D TB) : PathIn s' va D TB := by
  rcases h with ⟨observe, slotL, physL, vL, hav, hre, hid, htab, hpath, hD, hleaf, hroot, hcov, hphys, hwb⟩
  have hb : ∀ p : FullAddress, (∀ i < 8, TB (p.address.toNat + i)) → ∀ d,
      (BytesAt false (fun a => s'.mem[a]?) p d ↔ BytesAt false (fun a => s.mem[a]?) p d) := by
    intro p hp d
    constructor
    · intro hb' i hi; exact (hmem _ (hp i hi)).symm.trans (hb' i hi)
    · intro hb' i hi; exact (hmem _ (hp i hi)).trans (hb' i hi)
  have hrs := rootSlot_eq hsys va
  have hwm : ∀ a, WalkByte s.regs s.mem va a → s'.mem[a]? = s.mem[a]? := fun a ha => hmem a (hwb a ha)
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
    exact hwb a ((walkByte_congr s.regs s'.regs s.mem s'.mem va hrs hwm a).1 ha)

theorem walkFactE_of_pathIn (s : State) (va D : BitVec 64) (TB : Nat → Prop) (hH : Host20T s)
    (hEPD0 : _get_TCR_EL2_Type_EPD0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1)
    (hva : va.toNat < 2^48) (h : PathIn s va D TB) : WalkFactE s va D := by
  rcases h with ⟨observe, slotL, physL, vL, hav, hre, hid, htab, hpath, hD, hleaf, hroot, _, _, _⟩
  exact translate_walk_path_evT s hH va (MemM1.VA.varange va hva) hEPD0 hroot observe hav hre hid htab
    slotL physL vL hpath D hD hleaf

/-- TranslationAgrees only uses `walk va` at permitted `va`. -/
theorem agrees_walk_congr (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (w w' : BitVec 64 → List Nat) (s : State) (h : TranslationAgrees m w s)
    (hw : ∀ va acc al sz, m.permitted va acc al sz → w va = w' va) : TranslationAgrees m w' s := by
  intro u hu hum va acc al sz hp
  rcases h u hu hum va acc al sz hp with ⟨ad, t, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ti, W, he, hW⟩
  refine ⟨ad, t, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ti, W, he, ?_⟩
  unfold TTWReadsOK at hW ⊢
  rw [← hw va acc al sz hp]
  exact hW

/-- **E17 v3 at a later run state with the run's fixed walk.** From the kmap-instance inputs at `s`
    (Regs20, SCTLR_EL2.C = I = 1, Host20T, EPD0, and per mapped page the path inputs `PathIn` with
    table bytes `TB` and the leaf bits), any `s'` with the same system registers (`SysEq`) and the
    same table bytes satisfies `TranslationAgrees (kmap P) (walkK s.regs s.mem) s'`. -/
theorem agreesV3_step (s s' : State) (hR : MemM1.Witness.Regs20 s.regs)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (hI : _get_SCTLR_EL2_Type_I (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (hH : Host20T s)
    (hEPD0 : _get_TCR_EL2_Type_EPD0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1)
    (P : BitVec 64 → Option Page) (TB : Nat → Prop)
    (hP : ∀ (va : BitVec 64) (p : Page), va.toNat < 2^48 → P (va >>> 12) = some p →
      PathIn s va p.leaf TB ∧
        (if p.code then MemM1.WalkFactV.LeafBitsC p.leaf else MemM1.ConsumerD.LeafBitsD p.leaf))
    (hsys : SysEq2 s.regs s'.regs) (hmem : ∀ a, TB a → s'.mem[a]? = s.mem[a]?) :
    TranslationAgrees (kmap P) (walkK s.regs s.mem) s' := by
  have hR' := regs20 hsys hR
  have hC' : _get_SCTLR_EL2_Type_C (s'.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1 := by rw [hsys.sctlr]; exact hC
  have hI' : _get_SCTLR_EL2_Type_I (s'.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1 := by rw [hsys.sctlr]; exact hI
  have hH' := host20T hsys hH
  have hE' : _get_TCR_EL2_Type_EPD0 (s'.regs.bank_BitVec_64 .TCR_EL2) = 0#1 := by rw [hsys.tcr]; exact hEPD0
  have hA := MemM1.ConsumerV3F.agreesV3_kmapK_full s' hR' hC' hI' P (fun va p hva hp =>
    ⟨walkFactE_of_pathIn s' va p.leaf TB hH' hE' hva (pathIn_step s s' va p.leaf TB hsys hmem (hP va p hva hp).1),
      (hP va p hva hp).2⟩)
  refine agrees_walk_congr _ _ _ s' hA ?_
  intro va acc al sz hp
  rcases hp with ⟨hva, _, _, p, hpg, _⟩
  rcases (hP va p hva hpg).1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hwb⟩
  exact walkK_congr s.regs s'.regs s.mem s'.mem va (rootSlot_eq hsys va) (fun a ha => hmem a (hwb a ha))

#print axioms SysEq2.trans
#print axioms hde_pipeadv
#print axioms SysEq2_of_preFetch
#print axioms SysEq2_of_bool
#print axioms SysEq2_of_int
#print axioms SysEq2_of_clrGP
#print axioms SysEq2_of_fetchRegs
#print axioms SysEq2_of_bookkeeping
#print axioms SysEq_of_gpr
#print axioms SysEq_of_nzcv
#print axioms regs20
#print axioms host20T
#print axioms walkK_congr
#print axioms pathIn_step
#print axioms walkFactE_of_pathIn
#print axioms agrees_walk_congr
#print axioms agreesV3_step
end MemM1.StepInv2
