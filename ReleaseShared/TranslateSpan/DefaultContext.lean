-- Current machine facts for the catalogued deployment controls.
import TranslateSpan.MachineEntry
import NativeMteTagCheck.Primitive
import ArmCertPipe.FetchG

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk ArmCert.Translate.Model
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv NativeAccess TranslateSpan.EntryControls
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.DefaultMTE2
open NativeMteTagCheck

structure Core {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (profile : AccessProfile) (catalogue : ControlCatalogue) (k : Nat) (s : NativeState) : Prop where
  v1 : ChainInv spec config rows base offset budget k s
  closed : ClosedMembershipAt spec config rows mapping consumer (beforeFetchState s)
  placed : MemReloc.ImageOn scope image s loadBase mapping
  raw : RawImageAt spec.imageRows s.mem
  noUpd : ∀ write acc, DataShape write acc →
    NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true
  post : MemM1.MemReadD.PostRegs s.regs
  mode : HostEL0ModeAt s.regs
  debug : ExistingE11DebugAt s.regs
  feat : s.regs.FeatureImpl[7] = true ∧ s.regs.FeatureImpl[3] = false ∧
    s.regs.FeatureImpl[227] = false ∧ s.regs.FeatureImpl[111] = true
  dcache : currentDCache s.regs = true
  profileAt : ProfileAt profile s
  controls : DefaultAt catalogue s

def catalogue (s : NativeState) : ControlCatalogue :=
  ⟨s.regs.bank_BitVec_64 .TCR_EL2, s.regs.bank_BitVec_64 .SCTLR_EL2,
    s.regs.bank_BitVec_64 .HCR_EL2, s.regs.bank_BitVec_64 .SCR_EL3⟩

def checkMemory (catalogue : ControlCatalogue) (s : NativeState) : Bool :=
  decide (_get_SCTLR_EL2_Type_E0E (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1 ∧
    s.regs.PSTATE.TCO = 0#1 ∧
    _get_SCTLR_EL2_Type_TCF0 (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#2 ∧
    s.regs.bank_BitVec_64 .TCR_EL2 = catalogue.tcrEL2 ∧
    s.regs.bank_BitVec_64 .SCTLR_EL2 = catalogue.sctlrEL2 ∧
    s.regs.bank_BitVec_64 .HCR_EL2 = catalogue.hcrEL2 ∧
    s.regs.bank_BitVec_64 .SCR_EL3 = catalogue.scrEL3)

theorem memory_of_check (catalogue : ControlCatalogue) (s : NativeState) (pins : StepPins s)
    (features : ArmBridge.CruxGenGuarded.EntryActualFetch.EntryFeatures s.regs)
    (host : NativeMte2.HostPins s) (checked : checkMemory catalogue s = true) :
    MemM1.MemReadD.PostRegs s.regs ∧ DefaultAt catalogue s := by
  obtain ⟨endian,tco,tcf0,preparation⟩ := of_decide_eq_true checked
  exact ⟨⟨pins.spe,pins.el,pins.nrw,by simpa using pins.rme,features.vhe,
    by simpa using pins.f4,pins.scrns,pins.e2h,pins.tge,endian⟩,
    ⟨host,tco,tcf0,preparation⟩⟩

/-- Current getters and current table bytes, independent of branch execution. -/
def checkControls {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (profile : AccessProfile)
    (catalogue : ControlCatalogue) (pc : BitVec 64) (budget : Nat) (s : NativeState) : Bool :=
  checkStepPins s && (checkFeatures s && (checkDebug s && (checkQuiet budget s &&
  (checkGIC s && (checkMemory catalogue s && (checkNoUpdate spec s &&
  (checkCoreExtras s && (checkProfile profile s &&
  (decide (s.regs._PC = pc) && checkCurrentS1 spec config rows (beforeFetchState s))))))))))

theorem current_of_controls {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (profile : AccessProfile)
    (catalogue : ControlCatalogue) (pc : BitVec 64) (budget : Nat) (s : NativeState)
    (checked : checkControls spec config rows profile catalogue pc budget s = true) :
    CurrentS1At spec config rows (beforeFetchState s) := by
  simp only [checkControls,Bool.and_eq_true,decide_eq_true_eq] at checked
  obtain ⟨_,_,_,_,_,_,_,_,_,_,current⟩ := checked
  exact current_s1_of_check spec config rows (beforeFetchState s) current

theorem core_of_checks {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (profile : AccessProfile)
    (catalogue : ControlCatalogue) (mapping : BitVec 64 → Option Nat) (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (offsets : List Nat) (image : MemReloc.Image) (base : BitVec 64)
    (offset : Nat → BitVec 64) (budget : Nat) (s : NativeState)
    (checked : checkControls spec config rows profile catalogue (base + offset 0) budget s = true)
    (code : MachineEntry.checkPlaced offsets image base mapping s = true)
    (closed : ClosedMembershipAt spec config rows mapping consumer (beforeFetchState s)) :
    Core spec config rows mapping consumer (fun o => o ∈ offsets) image base base offset budget profile catalogue 0 s := by
  simp only [checkControls,Bool.and_eq_true,decide_eq_true_eq] at checked
  obtain ⟨pins,features,debug,quiet,gic,mem,noUpd,core,pf,pc,current⟩ := checked
  have sp := stepPins_of_check s pins
  have ef := features_of_check s features
  have de := debug_of_check s debug
  have ⟨feat,dcache⟩ := extras_of_check s ef core
  have profileAt := profile_of_check profile s sp ef pf
  have ⟨post,controls⟩ := memory_of_check catalogue s sp ef ⟨profileAt.host.el,profileAt.host.nrw,profileAt.host.aa64,profileAt.host.rme,
      profileAt.host.vhe,profileAt.host.ns,profileAt.host.e2h,profileAt.host.tge⟩ mem
  have currentS1 := current_s1_of_check spec config rows (beforeFetchState s) current
  have raw : RawImageAt spec.imageRows s.mem := by
    simp only [checkCurrentS1, Bool.and_eq_true] at current
    exact raw_image_of_check _ _ _ _ (beforeFetchState s).mem current.2.1
  exact ⟨⟨sp,ef,de.2,currentS1,by simpa using quiet_of_check budget s quiet,gic_of_check s gic,pc⟩,
    closed,MachineEntry.placed_of_check offsets image base mapping s code,raw,noUpdate_of_check spec s noUpd,
    post,mode_of_checks s sp ef,de.1,feat,dcache,profileAt,controls⟩

#print axioms checkMemory
#print axioms memory_of_check
#print axioms checkControls
#print axioms core_of_checks
#print axioms current_of_controls
end TranslateSpan.DefaultMTE2
