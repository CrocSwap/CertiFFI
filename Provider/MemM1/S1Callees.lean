import MemM1.S1T
import MemM1.Callees
import JointEL10.FieldsCore
import JointEL10.Get20
import JointEL10.Regime20
import Walk.S1StageOA
import Walk.S1EntryCallees
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.S1Callees
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault

/-! ### 1. hEn -/
drive_spec en_native, en_eq : fun (acctype : AccessType) (s : State) =>
  AArch64_S1Enabled .Regime_EL20 acctype s


/-! ### 2. hMin / hMax / hTxF -/
drive_spec min_native, min_eq : fun (s : State) =>
  AArch64_S1MinTxSZ .Regime_EL20 0#1 0#1 .TGx_4KB s

theorem minTx (wp : S1TTWParams) (s : State) (hd : wp.d128 = 0#1) (hds : wp.ds = 0#1)
    (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6) :
    ∀ t, Frame s t → ∃ m u,
      AArch64_S1MinTxSZ .Regime_EL20 wp.d128 wp.ds wp.tgx t = .ok m u ∧
        m ≤ (wp.txsz.toNat : Int) ∧ Frame t u := by
  intro t _
  rw [hd, hds, htg, htx, min_eq]
  observe_simp [Frame, min_native]
  exact ⟨_, _, ⟨rfl, rfl⟩, by decide, rfl, rfl, rfl⟩

drive_spec max_native, max_eq : fun (s : State) => AArch64_MaxTxSZ .TGx_4KB s

theorem maxTx (wp : S1TTWParams) (s : State) (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6) :
    ∀ t, Frame s t → ∃ m u,
      AArch64_MaxTxSZ wp.tgx t = .ok m u ∧ (wp.txsz.toNat : Int) ≤ m ∧ Frame t u := by
  intro t _
  rw [htg, htx, max_eq]
  observe_simp [Frame, max_native]
  split <;> exact ⟨_, _, ⟨rfl, rfl⟩, by decide, rfl, rfl, rfl⟩

drive_spec txf_native, txf_eq : fun (wp : S1TTWParams) (s : State) (hd : wp.d128 = 0#1)
    (hds : wp.ds = 0#1) (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6) =>
  AArch64_S1TxSZFaults .Regime_EL20 wp s

theorem txf (wp : S1TTWParams) (s : State) (hd : wp.d128 = 0#1) (hds : wp.ds = 0#1)
    (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6) :
    ∀ t, Frame s t → ∃ u, AArch64_S1TxSZFaults .Regime_EL20 wp t = .ok false u ∧ Frame t u := by
  intro t _
  rw [txf_eq wp t hd hds htg htx]
  observe_simp [Frame, txf_native]

/-! ### 3. hOOR -/
theorem oor (acctype : AccessType) (wp : S1TTWParams) :
    AArch64_VAIsOutOfRange 0#64 acctype .Regime_EL20 wp = false := by
  have h55 : BitVec.join1 [BitVec.access (0#64) 55] = 0#1 := by decide
  have h55' : (BitVec.setWidth 1 (BitVec.join1 [BitVec.access (0#64) 55]) == 0#1) = true := by decide
  have hu : BitVec.updateSubrange (0#64) 59 56 0#4 = 0#64 := by decide
  have h55u : BitVec.join1 [BitVec.access (BitVec.updateSubrange (0#64) 59 56 0#4) 55] = 0#1 := by decide
  have hz : (extzv 0#1 : BitVec 64) = 0#64 := by decide
  have hlu : (VARange.VARange_LOWER == VARange.VARange_UPPER) = false := rfl
  have hll : (VARange.VARange_LOWER == VARange.VARange_LOWER) = true := rfl
  have hr : (Regime.Regime_EL20 == Regime.Regime_EL20) = true := rfl
  have hz' : ∀ x : BitVec 64, 0#64 &&& x = 0#64 := fun x => BitVec.zero_and
  unfold AArch64_VAIsOutOfRange
  cases hm : (wp.mtx == 1#1) <;>
  simp [HasUnprivileged, is_zero_subrange, AArch64_GetVARange, hm, h55, h55', hu, h55u, hz, hlu, hll, hr, hz']

/-! ### 4. hAl -/
drive_spec al_native, al_eq : fun (acc : AccessDescriptor) (aligned : Bool) (ntlsmd : BitVec 1)
    (ma : MemoryAttributes) (s : State) (hmt : ma.memtype = .MemType_Normal) =>
  AArch64_S1HasAlignmentFault acc aligned ntlsmd ma s

theorem al (acc : AccessDescriptor) (aligned : Bool) (ntlsmd : BitVec 1) (ma : MemoryAttributes)
    (s : State) (hmt : ma.memtype = .MemType_Normal) :
    ∀ t, Frame s t → ∃ u,
      AArch64_S1HasAlignmentFault acc aligned ntlsmd ma t = .ok false u ∧ Frame t u := by
  intro t _
  rw [al_eq acc aligned ntlsmd ma t hmt]
  observe_simp [Frame, al_native]

/-! ### 6. hOA -/
theorem addr_congr (ia : BitVec 64) (w1 w2 : TTWState) (h1 : w1.baseaddress = w2.baseaddress)
    (h2 : w1.level = w2.level) (h3 : w1.contiguous = w2.contiguous) :
    S1StageOA.address ia w1 = S1StageOA.address ia w2 := by
  rcases w1 with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩
  rcases w2 with ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

def W0 : TTWState :=
  { (default : TTWState) with
    level := 3
    contiguous := 0#1
    baseaddress := ({paspace := .PAS_NonSecure, address := 0x505000000#56} : FullAddress) }

theorem addr_W0 : S1StageOA.address 0#64 W0 =
    {paspace := .PAS_NonSecure, address := 0x505000000#56} := by
  unfold S1StageOA.address
  congr 1

theorem oa (wp : S1TTWParams) (w : TTWState) (s : State) (hd : wp.d128 = 0#1)
    (htg : wp.tgx = .TGx_4KB) (hl : w.level = 3) (hc : w.contiguous = 0#1)
    (hb : w.baseaddress = {paspace := .PAS_NonSecure, address := 0x505000000#56}) :
    ∀ t, Frame s t → ∃ u, StageOA 0#64 wp.d128 wp.tgx w t =
      .ok {paspace := .PAS_NonSecure, address := 0x505000000#56} u ∧ Frame t u := by
  intro t _
  rcases S1StageOA.total 0#64 w t (by rw [hl]; decide) with ⟨u, h, f⟩
  refine ⟨u, ?_, f⟩
  rw [hd, htg, h, addr_congr 0#64 w W0 hb hl hc, addr_W0]

/-! ### 7. hDC / hMEC -/
theorem dc (s : State) :
    ∀ t, Frame s t → ∃ b u, AArch64_S1DCacheEnabled .Regime_EL20 t = .ok b u ∧ Frame t u :=
  fun t _ => S1EntryCallees.dcache_normal .Regime_EL20 (Or.inr rfl) t

drive_spec mec_native, mec_eq : fun (wp : S1TTWParams) (vr : VARange) (pas : PASpace)
    (desc : BitVec 128) (s : State) =>
  AArch64_S1OutputMECID wp .Regime_EL20 vr pas desc s

theorem mec (wp : S1TTWParams) (vr : VARange) (s : State) :
    ∀ (pas : PASpace) (desc : BitVec 128) t, Frame s t → ∃ m u,
      AArch64_S1OutputMECID wp .Regime_EL20 vr pas desc t = .ok m u ∧ Frame t u := by
  intro pas desc t _
  rw [mec_eq]
  observe_simp [Frame, mec_native]
  exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩

/-! ### 5. hPerm -/
drive_spec perm_native, perm_eq : fun (f : FaultRecord) (w : TTWState) (wp : S1TTWParams)
    (acc : AccessDescriptor) (s : State)
    (hPOE : s.regs.FeatureImpl[210] = false) (hGCS : s.regs.FeatureImpl[245] = false)
    (hPAN : s.regs.FeatureImpl[51] = false)
    (hpie : wp.pie = 0#1) (hwxn : wp.wxn = 0#1) (hel : acc.el = 0#2)
    (hacc : acc.acctype = .AccessType_GPR) (htag : acc.tagaccess = false)
    (hap : BitVec.setWidth 2 (Sail.BitVec.extractLsb w.permissions.ap 2 1) = 1#2)
    (hapt : w.permissions.ap_table = 0#2) =>
  AArch64_S1CheckPermissions f .Regime_EL20 w wp acc s

theorem perm (w : TTWState) (wp : S1TTWParams) (acc : AccessDescriptor) (s : State)
    (hPOE : s.regs.FeatureImpl[210] = false) (hGCS : s.regs.FeatureImpl[245] = false)
    (hPAN : s.regs.FeatureImpl[51] = false)
    (hpie : wp.pie = 0#1) (hwxn : wp.wxn = 0#1) (hel : acc.el = 0#2)
    (hacc : acc.acctype = .AccessType_GPR) (htag : acc.tagaccess = false)
    (hap : BitVec.setWidth 2 (Sail.BitVec.extractLsb w.permissions.ap 2 1) = 1#2)
    (hapt : w.permissions.ap_table = 0#2) :
    ∀ (f' : FaultRecord) t, f'.statuscode = .Fault_None → Frame s t → ∃ fc u,
      AArch64_S1CheckPermissions f' .Regime_EL20 w wp acc t = .ok fc u ∧
        fc.statuscode = .Fault_None ∧ Frame t u := by
  intro f' t hf ht
  rw [perm_eq f' w wp acc t (by rw [ht.1]; exact hPOE) (by rw [ht.1]; exact hGCS)
    (by rw [ht.1]; exact hPAN) hpie hwxn hel hacc htag hap hapt]
  observe_simp [Frame, perm_native]
  exact ⟨_, _, ⟨rfl, rfl⟩, hf, rfl, rfl, rfl⟩

#print axioms minTx
#print axioms maxTx
#print axioms txf
#print axioms oor
#print axioms al
#print axioms oa
#print axioms dc
#print axioms mec
#print axioms perm



end MemM1.S1Callees
