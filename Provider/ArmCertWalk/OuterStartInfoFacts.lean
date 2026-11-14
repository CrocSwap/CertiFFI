import ArmCertWalk.OuterStartInfoSource
import ArmCertWalk.TranslateMemoryFrames
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

def StartInfoResult (va : BitVec 64) (acc : AccessDescriptor) (size : Int) (state : State) :
    EStateM.Result (Sail.Error exception) State TranslationStartInfo → Prop
  | .ok info other => S1Normality.Frame state other ∧ info.ss = .SS_NonSecure ∧
      info.regime = .Regime_EL20 ∧ info.va = va ∧ info.accdesc = acc ∧ info.size = size
  | .error _ _ => False

theorem outer_start_info_total (va : BitVec 64) (acc : AccessDescriptor) (size : Int) (state : State)
    (host : HostRegimeAt state) :
    ∃ info other,
      AArch64_GetTranslationStartInfo .Regime_EL20 .SS_NonSecure acc va size state = .ok info other ∧
      S1Normality.Frame state other ∧ info.ss = .SS_NonSecure ∧ info.regime = .Regime_EL20 ∧
      info.va = va ∧ info.accdesc = acc ∧ info.size = size := by
  have good : StartInfoResult va acc size state (OuterStartInfoSource.native va acc size state) := by
    observe_simp [StartInfoResult, S1Normality.Frame, OuterStartInfoSource.native]
  have call := OuterStartInfoSource.complete va acc size state host.el3a64 host.noEl3a32 host.noRME host.a64 host.e2h
  rw [← call] at good
  cases result : AArch64_GetTranslationStartInfo .Regime_EL20 .SS_NonSecure acc va size state with
  | error err other => simp only [result, StartInfoResult] at good
  | ok info other => exact ⟨info, other, rfl, by simpa only [result, StartInfoResult] using good⟩

#print axioms outer_start_info_total
end ArmCertWalk
