-- Actual selected queries plus canonical buffer points, checked together at entry.
import TranslateSpan.CheckedEntry
import ArmCertValue.ReleaseGen
open Sail ArmFull ArmFull.Functions ArmCertWalk ArmCert.Translate.Model
open ArmCertValue
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.EntryMatrix

def pointVA (rs : List (Region × Nat)) (inputs : List (BitVec 64)) (r : Region) (j : Nat) : BitVec 64 :=
  BitVec.addInt (inputs.getD (totalL rs + r.pin) 0) (r.off + (j : Int))

def pointQuery (rs : List (Region × Nat)) (inputs : List (BitVec 64))
    (write : Region → Bool) (r : Region) (j : Nat) : AccessQuery :=
  ⟨pointVA rs inputs r j,⟨QueryDescriptors.data (write r),false⟩,1⟩

def points (rs : List (Region × Nat)) (inputs : List (BitVec 64))
    (write : Region → Bool) : List AccessQuery :=
  rs.flatMap (fun (p : Region × Nat) => (List.range p.2).map (pointQuery rs inputs write p.1))

theorem points_length (rs : List (Region × Nat)) (inputs : List (BitVec 64)) (write : Region → Bool) :
    (points rs inputs write).length = totalL rs := by
  simp only [points,List.length_flatMap,List.length_map,List.length_range]
  rfl

theorem point_member (rs : List (Region × Nat)) (inputs : List (BitVec 64)) (write : Region → Bool)
    (r : Region) (n j : Nat) (region : (r,n) ∈ rs) (bound : j < n) :
    pointQuery rs inputs write r j ∈ points rs inputs write := by
  exact List.mem_flatMap.mpr ⟨(r,n),region,List.mem_map.mpr ⟨j,List.mem_range.mpr bound,rfl⟩⟩

theorem checked_prefix {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {cap : Nat} {queries extra : List AccessQuery} {fuel : Nat} {entry : ArmCertWalk.State}
    (checked : CheckedEntry.checkQueries spec config rows mapping cap (queries ++ extra) fuel entry = true) :
    CheckedEntry.checkQueries spec config rows mapping cap queries fuel entry = true := by
  simp only [CheckedEntry.checkQueries,Bool.and_eq_true,List.all_append] at checked ⊢
  have bound := of_decide_eq_true checked.1
  rw [List.length_append] at bound
  exact ⟨by apply decide_eq_true; omega,checked.2.1⟩

#print axioms pointVA
#print axioms pointQuery
#print axioms points
#print axioms points_length
#print axioms point_member
#print axioms checked_prefix
end TranslateSpan.EntryMatrix
