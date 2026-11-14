import Walk.S1InitialWalkState
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
set_option maxRecDepth 1000000
namespace S1InitialStateFrame
open S1Normality

def Shape (wp : S1TTWParams) (w : TTWState) : Prop :=
  w.level = 0 ∧ w.istable = true ∧ w.baseaddress.paspace = .PAS_NonSecure ∧
    w.nG = 1#1 ∧ w.disch = wp.disch ∧ w.permissions.ap_table = 0#2 ∧
    w.permissions.uxn_table = 0#1 ∧ w.permissions.pxn_table = 0#1 ∧
    w.memattrs.memtype = .MemType_Normal ∧ w.memattrs.tags = .MemTag_Untagged

def Good (wp : S1TTWParams) (s : State) :
    EStateM.Result (Sail.Error exception) State TTWState → Prop
  | .ok w t => Frame s t ∧ Shape wp w
  | .error _ _ => False

theorem host_good (wp : S1TTWParams) (va : BitVec 64) (s : State)
    (hd : wp.d128 = 0#1) (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6) :
    Good wp s (S1InitialWalkState.host_native wp va s) := by
  have hStart := S1EntryCallees.start_zero wp hd htg htx
  observe_simp [Good, Frame, Shape, S1InitialWalkState.host_native]

theorem guest_good (wp : S1TTWParams) (va : BitVec 64) (s : State)
    (hd : wp.d128 = 0#1) (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6) :
    Good wp s (S1InitialWalkState.guest_native wp va s) := by
  have hStart := S1EntryCallees.start_zero wp hd htg htx
  observe_simp [Good, Frame, Shape, S1InitialWalkState.guest_native]

theorem total (wp : S1TTWParams) (va : BitVec 64) (regime : Regime) (s : State)
    (hregime : S1LeafBoth.Regimes regime)
    (hd : wp.d128 = 0#1) (hds : wp.ds = 0#1)
    (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) :
    ∃ w t, AArch64_S1InitialTTWState wp va regime .SS_NonSecure s = .ok w t ∧
      Frame s t ∧ Shape wp w := by
  have hg : Good wp s (AArch64_S1InitialTTWState wp va regime .SS_NonSecure s) := by
    rcases hregime with rfl | rfl
    · rw [S1InitialWalkState.guest_eq wp va s hd hds htg htx hEL3A64 hNoEL3A32]
      exact guest_good wp va s hd htg htx
    · rw [S1InitialWalkState.host_eq wp va s hd hds htg htx]
      exact host_good wp va s hd htg htx
  cases hr : AArch64_S1InitialTTWState wp va regime .SS_NonSecure s with
  | error e t => simp only [hr, Good] at hg
  | ok w t => exact ⟨w, t, rfl, by simpa only [hr, Good] using hg⟩
#print axioms total
end S1InitialStateFrame
