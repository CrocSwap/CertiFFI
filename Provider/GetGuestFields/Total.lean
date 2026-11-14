import GetGuestFields.Normal
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 150000
namespace GetGuestFields.Total
open S1Normality

theorem composed (vr : VARange) : Normal (GetGuestFields.composed vr) := by
  unfold GetGuestFields.composed
  apply bind_normal _ _ (GetGuestFields.Normal.initial)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.d128 wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.region wp vr)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.mair wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.mair2 wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.aie wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.wxn wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.ps wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.ee wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.sif wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.dc wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.ntlsmd wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.nv1 wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.cmow wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.ha wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.hd wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.ds wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.pie wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.pir wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.epan wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.pnch wp)
  intro wp
  apply bind_normal _ _ (GetGuestFields.Normal.haft wp)
  intro wp
  exact GetGuestFields.Normal.emec wp

theorem native (vr : VARange) : Normal (GetGuestComposition.native vr) := by
  rw [GetGuestFields.composed_eq]
  exact composed vr

theorem source (vr : VARange) : Normal (AArch64_S1TTWParamsEL10 vr) := by
  rw [GetGuestFields.source_eq]
  exact composed vr

theorem lower : Normal (AArch64_S1TTWParamsEL10 .VARange_LOWER) := source _
theorem upper : Normal (AArch64_S1TTWParamsEL10 .VARange_UPPER) := source _
#print axioms composed
#print axioms native
#print axioms source
#print axioms lower
#print axioms upper
end GetGuestFields.Total
