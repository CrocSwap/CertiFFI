import Walk.S1LogicalReferenceTypes
open Sail ArmFull
namespace S1LogicalReference

inductive EntryKind where
  | invalid | table | leaf
  deriving DecidableEq, BEq, Repr, Inhabited

def descriptorKind (level : Nat) (d : BitVec 64) : Evaluation EntryKind :=
  if level > 3 then .error (.malformedPath (level : Int))
  else if !d.getLsbD 0 then .ok .invalid
  else if d.getLsbD 1 then .ok (if level = 3 then .leaf else .table)
  else .ok (if level = 0 ∨ level = 3 then .invalid else .leaf)

def pageBase (d : BitVec 64) : BitVec 56 :=
  d.extractLsb' 12 36 |>.setWidth 56 |>.shiftLeft 12
def leafBits (level : Nat) : Nat := 12 + 9 * (3 - level)
def leafBase (level : Nat) (d : BitVec 64) : BitVec 56 :=
  BitVec.ofNat 56 (pageBase d |>.toNat |>.div (2 ^ leafBits level) |>.mul (2 ^ leafBits level))
def contiguous (c : Controls) (inheritedDisCH : Bool) (d : BitVec 64) : Bool :=
  !(c.pnch || inheritedDisCH) && d.getLsbD 52

def outputAddress (va : BitVec 64) (level : Nat) (base : FullAddress) (contig : Bool) : FullAddress :=
  let bits := leafBits level + if contig then 4 else 0
  {paspace := base.paspace
   address := BitVec.ofNat 56 (base.address.toNat / 2 ^ bits * 2 ^ bits + va.toNat % 2 ^ bits)}

def attributeIndex (aie : Bool) (d : BitVec 64) : BitVec 4 :=
  BitVec.ofNat 4 ((if aie && d.getLsbD 59 then 8 else 0) + (d.extractLsb' 2 3).toNat)
def mairByte (c : Controls) (index : BitVec 4) : BitVec 8 :=
  if index.toNat < 8 then (c.mair >>> (8 * index.toNat)).setWidth 8
  else (c.mair2 >>> (8 * (index.toNat - 8))).setWidth 8

def nv1Mode (c : Controls) : Bool := c.regime == .el10 && c.el2Enabled && c.nv1

def tablePermissions (c : Controls) (prior : TablePermissions) (d : BitVec 64) : TablePermissions :=
  if c.hpd || c.pie then prior
  else if nv1Mode c then
    {prior with ap := prior.ap ||| ((BitVec.ofBool (d.getLsbD 62)).setWidth 2 <<< 1)
                pxn := prior.pxn || d.getLsbD 60}
  else
    {ap := prior.ap ||| d.extractLsb' 61 2
     pxn := prior.pxn || d.getLsbD 59
     uxn := prior.uxn || d.getLsbD 60}

def classicPermissions (c : Controls) (d : BitVec 64) : ClassicPermissions :=
  let ap := if nv1Mode c then (BitVec.ofBool (d.getLsbD 7)).setWidth 2 <<< 1
    else d.extractLsb' 6 2
  let tracked := c.ha && c.hd && d.getLsbD 51
  {ap := if tracked then ap &&& 1#2 else ap
   pxn := d.getLsbD (if nv1Mode c then 54 else 53)
   uxn := if nv1Mode c then none else some (d.getLsbD 54)}

def permissionIndex (d : BitVec 64) : BitVec 4 :=
  BitVec.ofNat 4 (4 * (d.extractLsb' 53 2).toNat +
    2 * (BitVec.ofBool (d.getLsbD 51)).toNat + (BitVec.ofBool (d.getLsbD 6)).toNat)
def indirectPermissions (c : Controls) (d : BitVec 64) : IndirectPermissions :=
  let shift := 4 * (permissionIndex d).toNat
  {privileged := (c.pir >>> shift).setWidth 4
   unprivileged := (c.pire0 >>> shift).setWidth 4
   notDirty := d.getLsbD 7}

def leafPermissions (c : Controls) (table : TablePermissions) (d : BitVec 64) : Permissions :=
  {table
   leaf := if c.pie then .indirect (indirectPermissions c d) else .classic (classicPermissions c d)
   overlayIndex := if c.poe || c.e0poe then some ((d.extractLsb' 60 3).setWidth 4) else none}

def updateDescriptor (af dirty : Bool) (d : BitVec 64) : BitVec 64 :=
  let d := if af then d ||| 1024#64 else d
  if dirty then d &&& ~~~(128#64) else d

 theorem invalid_bit (level : Nat) (d : BitVec 64) (hl : level ≤ 3) (hd : d.getLsbD 0 = false) :
    descriptorKind level d = .ok .invalid := by
  simp only [descriptorKind, hd, show ¬level > 3 by omega, Bool.not_false, ↓reduceIte]
 theorem contiguous_pnch (c : Controls) (prior : Bool) (d : BitVec 64) (h : c.pnch = true) :
    contiguous c prior d = false := by simp [contiguous, h]
 theorem contiguous_disch (c : Controls) (d : BitVec 64) : contiguous c true d = false := by
  simp [contiguous]
 theorem attribute_no_aie (d : BitVec 64) : attributeIndex false d = (d.extractLsb' 2 3).setWidth 4 := by
  simp only [attributeIndex, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth_of_le (by decide)]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (d.extractLsb' 2 3).isLt (by decide))
 theorem no_update (d : BitVec 64) : updateDescriptor false false d = d := rfl
#print axioms invalid_bit
#print axioms contiguous_pnch
#print axioms attribute_no_aie
end S1LogicalReference
