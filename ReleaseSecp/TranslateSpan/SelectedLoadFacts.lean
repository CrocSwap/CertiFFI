-- Assemble the native load preconditions from static targets and actual current SSA bytes.
import NativeAccess.PairSelected
import TranslateSpan.SelectedBinding
open Sail ArmFull ArmCertWalk ArmCert.Translate.Model ArmBridge.Draft
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.SelectedLoadFacts
open ArmCertValue NativeAccess

/-- Pure target properties for the selector's finite address family. -/
def Targets (domain : BitVec 64 → Prop) (mapping : BitVec 64 → Option Nat)
    (start : BitVec 64) : Prop :=
  match PairGeometry.selected start with
  | .one16 => ∃ pa : BitVec 56, mapping start = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa
  | .two8 => ∃ pa : Fin 2 → BitVec 56,
      (∀ j, mapping (PairSplit.halfAddress start j) = some (pa j).toNat) ∧
      (∀ j, MemM1.MemReadIF.NotMMIO (pa j))
  | .bytes => (∀ j : Fin 16, domain (BitVec.addInt start (j.val : Int))) ∧
      ∃ pa : Fin 16 → BitVec 56,
        (∀ j, mapping (BitVec.addInt start (j.val : Int)) = some (pa j).toNat) ∧
        (∀ j, MemM1.MemReadIF.NotMMIO (pa j))

private instance (pa : BitVec 56) : Decidable (MemM1.MemReadIF.NotMMIO pa) := by
  unfold MemM1.MemReadIF.NotMMIO
  infer_instance

def checkRAM (mapping : BitVec 64 → Option Nat) (va : BitVec 64) : Bool :=
  match mapping va with
  | none => false
  | some pa => decide (pa < 2 ^ 56) && decide (MemM1.MemReadIF.NotMMIO (BitVec.ofNat 56 pa))

theorem ram_of_check (mapping : BitVec 64 → Option Nat) (va : BitVec 64)
    (checked : checkRAM mapping va = true) :
    ∃ pa : BitVec 56, mapping va = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa := by
  cases mapped : mapping va with
  | none => simp [checkRAM,mapped] at checked
  | some pa =>
    have facts : pa < 2 ^ 56 ∧ MemM1.MemReadIF.NotMMIO (BitVec.ofNat 56 pa) := by
      simpa only [checkRAM,mapped,Bool.and_eq_true,decide_eq_true_eq] using checked
    refine ⟨BitVec.ofNat 56 pa,?_,facts.2⟩
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt facts.1] using mapped

/-- At most sixteen actual selected starts; no unselected width is checked. -/
def checkTargets (mapping : BitVec 64 → Option Nat) (start : BitVec 64) : Bool :=
  match PairGeometry.selected start with
  | .one16 => checkRAM mapping start
  | .two8 => (List.ofFn (fun j : Fin 2 => PairSplit.halfAddress start j)).all (checkRAM mapping)
  | .bytes => (List.ofFn (fun j : Fin 16 => BitVec.addInt start (j.val : Int))).all (checkRAM mapping)

/-- Domain membership comes from the checked entry consumer, while bounded PA
and MMIO exclusion come from the finite static RAM check. -/
theorem targets_of_check (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop) (sites : List SelectedMap.Site) (code : List (BitVec 64))
    (site : SelectedMap.Site) (member : site ∈ sites) (read : site.write = false)
    (entry : ArmCertWalk.State)
    (closed : ClosedMembershipAt spec config rows mapping (SelectedMap.consumerMap sites code mapping table) entry)
    (checked : checkTargets mapping site.address = true) : Targets domain mapping site.address := by
  unfold Targets
  unfold checkTargets at checked
  generalize chosen : PairGeometry.selected site.address = c at checked ⊢
  cases c with
  | one16 => exact ram_of_check mapping site.address checked
  | two8 =>
    have each (j : Fin 2) : ∃ pa : BitVec 56,
        mapping (PairSplit.halfAddress site.address j) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa :=
      ram_of_check mapping _ (List.all_eq_true.mp checked _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
    exact ⟨fun j => (each j).choose,fun j => (each j).choose_spec.1,fun j => (each j).choose_spec.2⟩
  | bytes =>
    have each (j : Fin 16) : ∃ pa : BitVec 56,
        mapping (BitVec.addInt site.address (j.val : Int)) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa :=
      ram_of_check mapping _ (List.all_eq_true.mp checked _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
    refine ⟨?_,fun j => (each j).choose,fun j => (each j).choose_spec.1,fun j => (each j).choose_spec.2⟩
    intro j
    obtain ⟨acc,shape⟩ := HeapV2StepCerts.RawFetch.dataShape_read
    have hs : DataShape site.write acc := by rwa [read]
    have permit := SelectedMap.byte_member sites code mapping table site member chosen j acc hs false
    have permit' : (SelectedMap.consumerMap sites code mapping table).permitted
        (BitVec.addInt site.address (j.val : Int)) acc false 1 := by simpa [BitVec.addInt] using permit
    obtain ⟨data,dom,current⟩ := SelectedCurrent.point closed _ acc false 1 permit'
    exact dom

theorem binding (view : Physical.BytePA) (r : Region) (word : Nat)
    (mapping : BitVec 64 → Option Nat) (start : BitVec 64)
    (imm7 : BitVec 7) (Rn : BitVec 5) (x : NativeState)
    (source : LdpBytes.pairAddr x Rn imm7 = start)
    (span : SelectedBinding.At view r word mapping start) :
    PairSelected.Binding view r word mapping imm7 Rn x := by
  unfold PairSelected.Binding
  rw [source]
  unfold SelectedBinding.At at span
  cases chosen : PairGeometry.selected start <;> simpa only [chosen] using span

/-- No arbitrary future-state fact occurs here: RAM bytes concern this current x;
all mapping, permissions and fragment bindings are static. -/
theorem load_facts (domain : BitVec 64 → Prop) (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop) (sites : List SelectedMap.Site) (code : List (BitVec 64))
    (site : SelectedMap.Site) (member : site ∈ sites) (read : site.write = false)
    (view : Physical.BytePA) (r : Region) (word : Nat)
    (imm7 : BitVec 7) (Rn : BitVec 5) (x : NativeState)
    (source : LdpBytes.pairAddr x Rn imm7 = site.address)
    (span : SelectedBinding.At view r word mapping site.address)
    (targets : Targets domain mapping site.address)
    (data : BitVec 128)
    (payload : ∀ i, i < 16 → Physical.regionByte view x r (8 * word + i) = some (data.extractLsb' (8 * i) 8)) :
    PairSelected.LoadFacts domain mapping (SelectedMap.consumerMap sites code mapping table) imm7 Rn x := by
  unfold PairSelected.LoadFacts PairSelected.LoadOneData PairSelected.LoadSplitData PairSelected.LoadByteData
  rw [source]
  unfold SelectedBinding.At at span
  unfold Targets at targets
  generalize chosen : PairGeometry.selected site.address = c at span targets ⊢
  cases c with
  | one16 =>
    obtain ⟨pa,mapped,mmio⟩ := targets
    refine ⟨pa,data,mapped,mmio,?_,?_⟩
    · intro i hi
      have h := payload i hi
      rw [Physical.regionByte,span pa.toNat mapped i hi,Option.bind_some] at h
      exact h
    · intro acc shape
      have hs : DataShape site.write acc := by rwa [read]
      exact SelectedMap.one_member sites code mapping table site member chosen acc hs
  | two8 =>
    obtain ⟨pa,mapped,mmio⟩ := targets
    refine ⟨pa,data,mapped,mmio,?_,?_⟩
    · intro j i hi
      have h := payload (8 * j.val + i) (by omega)
      have lin := span j (pa j).toNat (mapped j) i hi
      rw [show 8 * word + (8 * j.val + i) = 8 * word + 8 * j.val + i by omega,
        Physical.regionByte,lin,Option.bind_some] at h
      rw [PairValue.halfValue_byte data j i hi]
      exact h
    · intro acc shape j
      have hs : DataShape site.write acc := by rwa [read]
      exact SelectedMap.half_member sites code mapping table site member chosen j acc hs
  | bytes =>
    obtain ⟨domains,pa,mapped,mmio⟩ := targets
    refine ⟨domains,pa,data,mapped,mmio,?_,?_⟩
    · intro j
      have h := payload j.val j.isLt
      rw [Physical.regionByte,span j (pa j).toNat (mapped j),Option.bind_some] at h
      exact h
    · intro acc shape j
      have hs : DataShape site.write acc := by rwa [read]
      have h := SelectedMap.byte_member sites code mapping table site member chosen j acc hs false
      simpa [BitVec.addInt] using h

#print axioms checkRAM
#print axioms ram_of_check
#print axioms checkTargets
#print axioms targets_of_check
#print axioms Targets
#print axioms binding
#print axioms load_facts
end TranslateSpan.SelectedLoadFacts
