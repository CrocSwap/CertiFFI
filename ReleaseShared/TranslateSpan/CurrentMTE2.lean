-- Branch-independent current machine facts for the MTE2-enabled path.
import TranslateSpan.MachineEntry
import ArmCertPipe.FetchG

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk ArmCert.Translate.Model
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv NativeAccess TranslateSpan.EntryControls
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.CurrentMTE2

structure Core {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (profile : AccessProfile) (k : Nat) (s : NativeState) : Prop where
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
  mte2 : s.regs.FeatureImpl[134] = true
  tco : s.regs.PSTATE.TCO = 1#1

def checkMemory (s : NativeState) : Bool :=
  decide (_get_SCTLR_EL2_Type_E0E (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1 ∧
    s.regs.FeatureImpl[134] = true ∧ s.regs.PSTATE.TCO = 1#1)

theorem memory_of_check (s : NativeState) (pins : StepPins s)
    (features : ArmBridge.CruxGenGuarded.EntryActualFetch.EntryFeatures s.regs)
    (checked : checkMemory s = true) :
    MemM1.MemReadD.PostRegs s.regs ∧ s.regs.FeatureImpl[134] = true ∧ s.regs.PSTATE.TCO = 1#1 := by
  obtain ⟨endian,mte2,tco⟩ := of_decide_eq_true checked
  exact ⟨⟨pins.spe,pins.el,pins.nrw,by simpa using pins.rme,features.vhe,
    by simpa using pins.f4,pins.scrns,pins.e2h,pins.tge,endian⟩,mte2,tco⟩

theorem clearTag_dataShape (write : Bool) (acc : AccessDescriptor) (shape : DataShape write acc) :
    DataShape write {acc with tagchecked := false} := by
  exact ⟨shape.acctype,shape.el,shape.ss,shape.read,shape.write,shape.tagaccess,
    shape.transactional,shape.nonfault,shape.contiguous,shape.firstfault,shape.first,shape.ls64⟩

theorem tco_of_nonProj {r s : Regs}
    (frame : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap r s) :
    s.PSTATE.TCO = r.PSTATE.TCO := by
  have eq := congrArg (fun x : Regs => x.PSTATE.TCO) frame
  exact eq

/-- Current getters and current table bytes, independent of branch execution. -/
def checkControls {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (profile : AccessProfile)
    (pc : BitVec 64) (budget : Nat) (s : NativeState) : Bool :=
  checkStepPins s && (checkFeatures s && (checkDebug s && (checkQuiet budget s &&
  (checkGIC s && (checkMemory s && (checkNoUpdate spec s &&
  (checkCoreExtras s && (checkProfile profile s &&
  (decide (s.regs._PC = pc) && checkCurrentS1 spec config rows (beforeFetchState s))))))))))

theorem current_of_controls {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (profile : AccessProfile)
    (pc : BitVec 64) (budget : Nat) (s : NativeState)
    (checked : checkControls spec config rows profile pc budget s = true) :
    CurrentS1At spec config rows (beforeFetchState s) := by
  simp only [checkControls,Bool.and_eq_true,decide_eq_true_eq] at checked
  obtain ⟨_,_,_,_,_,_,_,_,_,_,current⟩ := checked
  exact current_s1_of_check spec config rows (beforeFetchState s) current

theorem core_of_checks {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (profile : AccessProfile)
    (mapping : BitVec 64 → Option Nat) (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (offsets : List Nat) (image : MemReloc.Image) (base : BitVec 64)
    (offset : Nat → BitVec 64) (budget : Nat) (s : NativeState)
    (checked : checkControls spec config rows profile (base + offset 0) budget s = true)
    (code : MachineEntry.checkPlaced offsets image base mapping s = true)
    (closed : ClosedMembershipAt spec config rows mapping consumer (beforeFetchState s)) :
    Core spec config rows mapping consumer (fun o => o ∈ offsets) image base base offset budget profile 0 s := by
  simp only [checkControls,Bool.and_eq_true,decide_eq_true_eq] at checked
  obtain ⟨pins,features,debug,quiet,gic,mem,noUpd,core,pf,pc,current⟩ := checked
  have sp := stepPins_of_check s pins
  have ef := features_of_check s features
  have de := debug_of_check s debug
  have ⟨feat,dcache⟩ := extras_of_check s ef core
  have ⟨post,mte2,tco⟩ := memory_of_check s sp ef mem
  have currentS1 := current_s1_of_check spec config rows (beforeFetchState s) current
  have raw : RawImageAt spec.imageRows s.mem := by
    simp only [checkCurrentS1, Bool.and_eq_true] at current
    exact raw_image_of_check _ _ _ _ (beforeFetchState s).mem current.2.1
  exact ⟨⟨sp,ef,de.2,currentS1,by simpa using quiet_of_check budget s quiet,gic_of_check s gic,pc⟩,
    closed,MachineEntry.placed_of_check offsets image base mapping s code,raw,noUpdate_of_check spec s noUpd,
    post,mode_of_checks s sp ef,de.1,feat,dcache,profile_of_check profile s sp ef pf,mte2,tco⟩

#print axioms checkMemory
#print axioms memory_of_check
#print axioms clearTag_dataShape
#print axioms tco_of_nonProj
#print axioms checkControls
#print axioms core_of_checks
#print axioms current_of_controls
end TranslateSpan.CurrentMTE2
