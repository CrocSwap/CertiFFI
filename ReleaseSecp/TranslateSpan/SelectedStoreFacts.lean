-- Static selected mapping/output checks supply all native store prerequisites.
import TranslateSpan.SelectedLoadFacts
import TranslateSpan.QueryDescriptors
open Sail ArmFull ArmCertWalk ArmCert.Translate.Model ArmBridge.Draft
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.SelectedStoreFacts
open ArmCertValue NativeAccess

theorem targets_of_check (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop) (sites : List SelectedMap.Site) (code : List (BitVec 64))
    (site : SelectedMap.Site) (member : site ∈ sites) (write : site.write = true)
    (entry : ArmCertWalk.State)
    (closed : ClosedMembershipAt spec config rows mapping (SelectedMap.consumerMap sites code mapping table) entry)
    (checked : SelectedLoadFacts.checkTargets mapping site.address = true) :
    SelectedLoadFacts.Targets domain mapping site.address := by
  unfold SelectedLoadFacts.Targets
  unfold SelectedLoadFacts.checkTargets at checked
  generalize chosen : PairGeometry.selected site.address = c at checked ⊢
  cases c with
  | one16 => exact SelectedLoadFacts.ram_of_check mapping site.address checked
  | two8 =>
    have each (j : Fin 2) : ∃ pa : BitVec 56,
        mapping (PairSplit.halfAddress site.address j) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa :=
      SelectedLoadFacts.ram_of_check mapping _ (List.all_eq_true.mp checked _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
    exact ⟨fun j => (each j).choose,fun j => (each j).choose_spec.1,fun j => (each j).choose_spec.2⟩
  | bytes =>
    have each (j : Fin 16) : ∃ pa : BitVec 56,
        mapping (BitVec.addInt site.address (j.val : Int)) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa :=
      SelectedLoadFacts.ram_of_check mapping _ (List.all_eq_true.mp checked _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
    refine ⟨?_,fun j => (each j).choose,fun j => (each j).choose_spec.1,fun j => (each j).choose_spec.2⟩
    intro j
    have shape : DataShape site.write (QueryDescriptors.data true) := by
      rw [write]; exact QueryDescriptors.data_shape true
    have permit := SelectedMap.byte_member sites code mapping table site member chosen j _ shape false
    have permit' : (SelectedMap.consumerMap sites code mapping table).permitted
        (BitVec.addInt site.address (j.val : Int)) (QueryDescriptors.data true) false 1 := by
      simpa [BitVec.addInt] using permit
    obtain ⟨data,dom,current⟩ := SelectedCurrent.point closed _ _ false 1 permit'
    exact dom

/-- A pure byte-footprint property; it refers to no machine state. -/
def OutputSafe {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (view : Physical.BytePA) (r : Region) (word : Nat) (D : Nat → Prop) : Prop :=
  ∀ i, i < 16 → ∀ pa, view r (8 * word + i) = some pa →
    ¬ (rowsFootprint spec.imageRows).byte pa ∧ D pa

theorem store_facts (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (mapping : BitVec 64 → Option Nat) (table D : Nat → Prop)
    (sites : List SelectedMap.Site) (code : List (BitVec 64))
    (site : SelectedMap.Site) (member : site ∈ sites) (write : site.write = true)
    (view : Physical.BytePA) (r : Region) (word : Nat)
    (imm7 : BitVec 7) (Rn : BitVec 5) (x : NativeState)
    (source : LdpBytes.pairAddr x Rn imm7 = site.address)
    (span : SelectedBinding.At view r word mapping site.address)
    (targets : SelectedLoadFacts.Targets domain mapping site.address)
    (output : OutputSafe spec view r word D) :
    PairSelected.StoreFacts domain spec mapping (SelectedMap.consumerMap sites code mapping table) D imm7 Rn x := by
  unfold PairSelected.StoreFacts PairSelected.StoreOneData PairSelected.StoreSplitData PairSelected.StoreByteData
  rw [source]
  unfold SelectedBinding.At at span
  unfold SelectedLoadFacts.Targets at targets
  generalize chosen : PairGeometry.selected site.address = c at span targets ⊢
  cases c with
  | one16 =>
    obtain ⟨pa,mapped,mmio⟩ := targets
    refine ⟨pa,mapped,mmio,?_,?_,?_⟩
    · intro i hi
      exact (output i hi _ (span pa.toNat mapped i hi)).1
    · intro i hi
      exact (output i hi _ (span pa.toNat mapped i hi)).2
    · intro acc shape
      have hs : DataShape site.write acc := by rwa [write]
      exact SelectedMap.one_member sites code mapping table site member chosen acc hs
  | two8 =>
    obtain ⟨pa,mapped,mmio⟩ := targets
    have safe (j : Fin 2) (i : Nat) (hi : i < 8) :=
      output (8 * j.val + i) (by omega) ((pa j).toNat + i)
        (by simpa only [Nat.add_assoc] using span j (pa j).toNat (mapped j) i hi)
    refine ⟨pa,mapped,mmio,?_,?_,?_⟩
    · intro j i hi; exact (safe j i hi).1
    · intro j i hi; exact (safe j i hi).2
    · intro acc shape j
      have hs : DataShape site.write acc := by rwa [write]
      exact SelectedMap.half_member sites code mapping table site member chosen j acc hs
  | bytes =>
    obtain ⟨domains,pa,mapped,mmio⟩ := targets
    refine ⟨domains,pa,mapped,mmio,?_,?_,?_⟩
    · intro j; exact (output j.val j.isLt _ (span j (pa j).toNat (mapped j))).1
    · intro j; exact (output j.val j.isLt _ (span j (pa j).toNat (mapped j))).2
    · intro acc shape j
      have hs : DataShape site.write acc := by rwa [write]
      have h := SelectedMap.byte_member sites code mapping table site member chosen j acc hs false
      simpa [BitVec.addInt] using h

#print axioms targets_of_check
#print axioms OutputSafe
#print axioms store_facts
end TranslateSpan.SelectedStoreFacts
