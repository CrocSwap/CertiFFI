-- Fixed-entry machine invariant assembly. All execution proofs consume its result internally.
import TranslateSpan.EntryControls
import ArmCertTranslateModel.CurrentS1Checks
import ArmCertValue.EntrySnapshot

open Sail ArmFull ArmFull.Functions ArmCertWalk ArmCert.Translate.Model ArmBridge.Draft
open ArmBridge.CruxGenGuarded ArmCertPipe NativeAccess
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.MachineEntry
open EntryControls

/-- Map and check each required image byte in the actual entry memory.
Missing virtual mappings, image bytes, and RAM bytes all reject. -/
def checkPlaced (offsets : List Nat) (image : MemReloc.Image) (base : BitVec 64)
    (mapping : BitVec 64 → Option Nat) (s : NativeState) : Bool :=
  offsets.all fun o =>
    match image o, mapping (MemReloc.imageAddress base o) with
    | some b, some pa => s.mem[pa]? == some b
    | _, _ => false

theorem placed_of_check (offsets : List Nat) (image : MemReloc.Image) (base : BitVec 64)
    (mapping : BitVec 64 → Option Nat) (s : NativeState)
    (checked : checkPlaced offsets image base mapping s = true) :
    MemReloc.ImageOn (fun o => o ∈ offsets) image s base mapping := by
  intro o member
  have h := List.all_eq_true.mp checked o member
  cases im : image o <;> cases mp : mapping (MemReloc.imageAddress base o) <;> simp_all

def checkPresent (rs : List (ArmCertValue.Region × Nat)) (view : ArmCertValue.Physical.BytePA)
    (s : NativeState) : Bool :=
  rs.all fun (r,n) => (List.range n).all fun j => (ArmCertValue.Physical.regionByte view s r j).isSome

theorem present_of_check (rs : List (ArmCertValue.Region × Nat)) (view : ArmCertValue.Physical.BytePA)
    (s : NativeState) (checked : checkPresent rs view s = true) :
    ∀ g j i k, ArmCertValue.memBL rs 0 g j = some (i,k) →
      (ArmCertValue.Physical.regionByte view s g j).isSome = true := by
  have each : ∀ r n, (r,n) ∈ rs → ∀ j < n,
      (ArmCertValue.Physical.regionByte view s r j).isSome = true := by
    intro r n hm j hj
    exact List.all_eq_true.mp (List.all_eq_true.mp checked (r,n) hm) j (List.mem_range.mpr hj)
  clear checked
  intro g j i k
  generalize hbase : 0 = base
  clear hbase
  induction rs generalizing base with
  | nil => simp [ArmCertValue.memBL]
  | cons p rs ih =>
    obtain ⟨r,n⟩ := p
    intro h
    simp only [ArmCertValue.memBL] at h
    split at h
    · next hit =>
      obtain ⟨rfl,hj⟩ := hit
      exact each _ _ List.mem_cons_self _ hj
    · exact ih (fun r n hm => each r n (List.mem_cons_of_mem _ hm)) (base+n) h

/-- Check every scalar, the raw table bytes and translation controls, and the PC
of the declared initial instruction. All reads are from this entry. -/
def checkControls {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (profile : AccessProfile)
    (pc : BitVec 64) (budget : Nat) (s : NativeState) : Bool :=
  checkStepPins s && (checkFeatures s && (checkDebug s && (checkQuiet budget s &&
  (checkGIC s && (checkMemoryControls s && (checkBranchBase s && (checkBranchExtras s &&
  (checkNoUpdate spec s && (checkCoreExtras s && (checkProfile profile s &&
  (decide (s.regs._PC = pc) && checkCurrentS1 spec config rows (beforeFetchState s))))))))))))

/-- Generic join. The two program-dependent facts are provided internally by
the finite query and entry snapshot theorems. -/
theorem inv_of_checks {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (profile : AccessProfile)
    (mapping : BitVec 64 → Option Nat) (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (offsets : List Nat) (image : MemReloc.Image) (base : BitVec 64)
    (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (s : NativeState)
    (checked : checkControls spec config rows profile (base + offset 0) budget s = true)
    (code : checkPlaced offsets image base mapping s = true)
    (closed : ClosedMembershipAt spec config rows mapping consumer (beforeFetchState s))
    (init : extra 0 s) :
    ChainInvG spec config rows mapping consumer (fun o => o ∈ offsets) image base base offset budget
      (fun k x => extra k x ∧ ProfileAt profile x) 0 s := by
  simp only [checkControls, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨pins,features,debug,quiet,gic,post,branch,gcs,noUpd,core,pf,pc,current⟩ := checked
  have sp := stepPins_of_check s pins
  have ef := features_of_check s features
  have de := debug_of_check s debug
  have ⟨feat,dcache⟩ := extras_of_check s ef core
  have currentS1 := current_s1_of_check spec config rows (beforeFetchState s) current
  have raw : RawImageAt spec.imageRows s.mem := by
    simp only [checkCurrentS1, Bool.and_eq_true] at current
    exact raw_image_of_check _ _ _ _ (beforeFetchState s).mem current.2.1
  exact ⟨⟨⟨sp,ef,de.2,currentS1,by simpa using quiet_of_check budget s quiet,gic_of_check s gic,pc⟩,
      closed,placed_of_check offsets image base mapping s code,branch_of_check s ef branch gcs⟩,
    raw,noUpdate_of_check spec s noUpd,post2_of_check s sp ef post,mode_of_checks s sp ef,de.1,
    feat,dcache,init,profile_of_check profile s sp ef pf⟩

#print axioms checkPlaced
#print axioms placed_of_check
#print axioms checkPresent
#print axioms present_of_check
#print axioms checkControls
#print axioms inv_of_checks
end TranslateSpan.MachineEntry
