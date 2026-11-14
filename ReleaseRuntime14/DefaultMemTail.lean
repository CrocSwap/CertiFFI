-- Fetched-state interface matching the generic default memory continuation.
import ArmCertMemPipe.EntryMemG
import ArmCertMemPipe.EvD
import DefaultActionControls
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)
open NativeMteTagCheck
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultMemTail
structure GCtxDefault {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (X : NativeState → Prop)
    (catalogue : ControlCatalogue) (x : NativeState) : Prop where
  closed : ClosedMembershipAt spec config rows mapping m x
  prog : X x
  raw : RawImageAt spec.imageRows x.mem
  noUpd : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
    NoUpdateRows {spec.params with haft := hostHAFT x.regs} acc spec.imageRows = true
  post : MemM1.MemReadD.PostRegs x.regs
  current : CurrentS1At spec config rows x
  controls : DefaultAt catalogue x
  allowed : TagStatusOK x
  mode : HostEL0ModeAt x.regs
  debug : ExistingE11DebugAt x.regs
  feat : x.regs.FeatureImpl[7] = true ∧ x.regs.FeatureImpl[3] = false ∧
    x.regs.FeatureImpl[227] = false ∧ x.regs.FeatureImpl[111] = true
  dcache : currentDCache x.regs = true

def MemTailAt (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (Ctx : NativeState → Prop) (D : Nat → Prop)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (source : NativeState) (next : BitVec 64)
    (us : List (RegBind.Reg × RegBind.Upd)) (Pay : NativeState → NativeState → Prop) (cost : Nat) : Prop :=
  ∀ (fetched : NativeState) (enc0 : __InstrEnc) (budget : Nat),
    StepPins fetched → NativeEntryInput.Input source fetched → MetadataGuard fetched →
    HookQuiet (budget + 1) fetched → fetched.regs.ShouldAdvanceIT = false →
    fetched.regs.ShouldAdvanceSS = true →
    CurrentS1At spec config rows fetched → Ctx fetched →
    ∃ (sp a fin : NativeState) (written : Nat → Prop),
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source w enc0 fetched = .ok () fin ∧
      NativeEntryContract.Frame writes (actionState w sp K) a ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧
      WritesOnly written (fun x => fetched.mem[x]?) (fun x => fin.mem[x]?) ∧
      Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ x, written x → D x) ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs._PC = next ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs ∧
      (∀ x : Nat, (fetched.mem[x]?).isSome → (fin.mem[x]?).isSome) ∧
      RegBind.Holds us fetched fin ∧ Pay fetched fin ∧
      ∃ draws, ChoiceDelta fetched fin draws ∧ draws ≤ cost

end ReleaseProfile.DefaultMemTail
