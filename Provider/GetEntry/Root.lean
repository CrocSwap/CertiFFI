import GetEntry.InitialEntryAddress
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1EntryRoot
open S1Normality

def word (r : Regs) (regime : Regime) (va : BitVec 64) : BitVec 128 :=
  if regime == .Regime_EL20 then
    if (AArch64_GetVARange va == .VARange_LOWER) then
      Sail.BitVec.zeroExtend
        (Sail.BitVec.updateSubrange (r.bank_BitVec_128 ._TTBR0_EL2) 47 1
          (Sail.BitVec.slice (r.bank_BitVec_64 .HTTBR) 1 47)) 128
    else Sail.BitVec.zeroExtend (r.bank_BitVec_128 .TTBR1_EL2) 128
  else
    if (AArch64_GetVARange va == .VARange_LOWER) then
      Sail.BitVec.zeroExtend
        (Sail.BitVec.updateSubrange (r.bank_BitVec_128 ._TTBR0_EL1) 63 0
          (Sail.BitVec.slice (r.bank_BitVec_64 .TTBR0_NS) 0 64)) 128
    else
      Sail.BitVec.zeroExtend
        (Sail.BitVec.updateSubrange (r.bank_BitVec_128 ._TTBR1_EL1) 63 0
          (Sail.BitVec.slice (r.bank_BitVec_64 .TTBR1_NS) 0 64)) 128

def base (wp : S1TTWParams) (r : Regs) (regime : Regime) (va : BitVec 64) : BitVec 56 :=
  Align_bits (Sail.BitVec.updateSubrange (0#56) 47 1
    (Sail.BitVec.extractLsb (word r regime va) 47 1))
    (_shl_int_general 1 (48 - ((3 - AArch64_S1StartLevel wp) * 9 + 12) + 3))

def slot (wp : S1TTWParams) (r : Regs) (regime : Regime) (va : BitVec 64) : FullAddress :=
  S1InitialEntryAddress.address va {address := base wp r regime va, paspace := .PAS_NonSecure}

def Good (wp : S1TTWParams) (regime : Regime) (va : BitVec 64) (s : State) :
    EStateM.Result (Sail.Error exception) State TTWState → Prop
  | .ok w t => Frame s t ∧ w.baseaddress.address = base wp s.regs regime va
  | .error _ _ => False

theorem host_good (wp : S1TTWParams) (va : BitVec 64) (s : State) :
    Good wp .Regime_EL20 va s (S1InitialWalkState.host_native wp va s) := by
  observe_simp [Good, Frame, base, word, S1InitialWalkState.host_native]

theorem guest_good (wp : S1TTWParams) (va : BitVec 64) (s : State) :
    Good wp .Regime_EL10 va s (S1InitialWalkState.guest_native wp va s) := by
  observe_simp [Good, Frame, base, word, S1InitialWalkState.guest_native]

theorem total (wp : S1TTWParams) (va : BitVec 64) (regime : Regime) (s : State)
    (hRegime : S1LeafBoth.Regimes regime)
    (hd : wp.d128 = 0#1) (hds : wp.ds = 0#1)
    (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) :
    ∃ w t, AArch64_S1InitialTTWState wp va regime .SS_NonSecure s = .ok w t ∧
      Frame s t ∧ S1InitialStateFrame.Shape wp w ∧
      w.baseaddress.address = base wp s.regs regime va := by
  rcases S1InitialStateFrame.total wp va regime s hRegime hd hds htg htx hEL3A64 hNoEL3A32 with
    ⟨w, t, hr, hf, hs⟩
  have hg : Good wp regime va s (AArch64_S1InitialTTWState wp va regime .SS_NonSecure s) := by
    rcases hRegime with rfl | rfl
    · rw [S1InitialWalkState.guest_eq wp va s hd hds htg htx hEL3A64 hNoEL3A32]
      exact guest_good wp va s
    · rw [S1InitialWalkState.host_eq wp va s hd hds htg htx]
      exact host_good wp va s
  rw [hr] at hg
  exact ⟨w, t, hr, hf, hs, hg.2⟩
#print axioms total

theorem initial_slot (wp : S1TTWParams) (va : BitVec 64) (regime : Regime) (s : State)
    (hRegime : S1LeafBoth.Regimes regime)
    (hd : wp.d128 = 0#1) (hds : wp.ds = 0#1)
    (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) :
    ∃ w t u, AArch64_S1InitialTTWState wp va regime .SS_NonSecure s = .ok w t ∧
      AArch64_S1SLTTEntryAddress w.level wp va w.baseaddress t =
        .ok (slot wp s.regs regime va) u ∧
      Frame s u ∧ S1InitialStateFrame.Shape wp w := by
  rcases total wp va regime s hRegime hd hds htg htx hEL3A64 hNoEL3A32 with
    ⟨w, t, hi, hf, hs, hb⟩
  have hp := hs.2.2.1
  have hbase : w.baseaddress =
      {address := base wp s.regs regime va, paspace := .PAS_NonSecure} := by
    cases he : w.baseaddress with
    | mk pas addr =>
      simp only [he] at hp hb
      simp only [he, hp, hb]
  rcases S1InitialEntryAddress.total wp va w.baseaddress t hd htg htx with
    ⟨u, ha, hr2, hm2, he2⟩
  refine ⟨w, t, u, hi, ?_, ⟨hr2.trans hf.1, hm2.trans hf.2.1, he2.trans hf.2.2⟩, hs⟩
  simpa only [hs.1, hbase, slot] using ha
#print axioms initial_slot

end S1EntryRoot
