import ArmCertWalk.OuterStartInfoFacts
import ArmCertWalk.NativeFullTranslateTotal
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

/-- The REAL remaining source action, retaining the complete debug checker
and exact translation-end event. It makes no debug-off assumption. -/
def translation_debug_finish (va : BitVec 64) (acc : AccessDescriptor) (size : Int)
    (address : AddressDescriptor) : SailM AddressDescriptor := do
  let fault ← AArch64_CheckDebug va acc size
  let result := {address with fault := fault, vaddress := Sail.BitVec.zeroExtend va 64}
  end_translation result
  pure result

/-- Internal composition from PAST actual source calls. The remaining debug
checker executes exactly as in the original source, including faults/halts.
These call equations are not entry hypotheses for any caller theorem. -/
theorem translate_if_residual_eq (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool)
    (size : Int) (initial : State) (regime : Regime) (afterRegime : State)
    (info : TranslationStartInfo) (afterInfo : State) (address : AddressDescriptor) (ready : State)
    (fetch : acc.acctype = .AccessType_IFETCH)
    (regimeCall : TranslationRegime acc.el initial = .ok regime afterRegime)
    (infoCall : AArch64_GetTranslationStartInfo regime acc.ss acc va size afterRegime = .ok info afterInfo)
    (fullCall : AArch64_FullTranslate va acc aligned
      {afterInfo with events := afterInfo.events.push (.translationStart info)} = .ok address ready)
    (noFault : address.fault.statuscode = .Fault_None)
    (noRME : HaveRME () ready = .ok false ready) :
    AArch64_TranslateAddress va acc aligned size initial = translation_debug_finish va acc size address ready := by
  have noneNe : ((.Fault_None : Fault) != .Fault_None) = false := rfl
  have fetchEq : (acc.acctype == .AccessType_IFETCH) = true := by rw [fetch]; rfl
  have fetchNe : (acc.acctype != .AccessType_IFETCH) = false := by rw [fetch]; rfl
  unfold AArch64_TranslateAddress
  simp only [Bind.bind, EStateM.bind, readReg, PreSail.readReg_apply, fetchEq, Bool.true_or,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure,
    start_translation, ArmFull.ConcurrencyInterfaceV1.sail_translation_start,
    PreSail.sail_translation_start, PreSail.logEvent, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet]
  simp only [regimeCall, infoCall]
  simp only [fullCall, IsFault, noFault, noneNe, Bool.not_false, Bool.true_and, fetchNe,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, EStateM.bind, EStateM.pure, noRME,
    Bool.false_and, fetchEq, Bool.and_true, Bool.true_or, Bool.not_true]
  cases debugCall : AArch64_CheckDebug va acc size ready <;>
    simp only [translation_debug_finish, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, debugCall]

#print axioms translate_if_residual_eq
end ArmCertWalk
