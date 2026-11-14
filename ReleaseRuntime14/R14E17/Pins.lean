import R14E17.Table

/-! runtime14 pins from the entry state's read view (454f/b669: LeanRuntime.Native.View). Kept free
of imports. Instantiate `gpr:= fun i => (view mapping e).gpr (BitVec.ofNat 5 i)` (31 = SP) and
`byte := (view mapping e).byte`. The two indirect forms:
* "x0+UBFM64[1,63](x1)+24": the ByteArray data byte at index x1 >> 1 (unboxed scalar);
* "x0+mem64[x1+8]+24": the data byte at the index read from the boxed scalar's word at x1 + 8. -/

set_option autoImplicit false
namespace R14E17

/-- Little-endian 64-bit read through a byte view (explicit sum: no List.range unfolding in kernel checks). -/
def mem64 (byte : BitVec 64 → BitVec 8) (a : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((byte (a + BitVec.ofNat 64 0)).toNat * 2 ^ (8 * 0) + (byte (a + BitVec.ofNat 64 1)).toNat * 2 ^ (8 * 1) +
    (byte (a + BitVec.ofNat 64 2)).toNat * 2 ^ (8 * 2) + (byte (a + BitVec.ofNat 64 3)).toNat * 2 ^ (8 * 3) +
    (byte (a + BitVec.ofNat 64 4)).toNat * 2 ^ (8 * 4) + (byte (a + BitVec.ofNat 64 5)).toNat * 2 ^ (8 * 5) +
    (byte (a + BitVec.ofNat 64 6)).toNat * 2 ^ (8 * 6) + (byte (a + BitVec.ofNat 64 7)).toNat * 2 ^ (8 * 7))

def indirectVA (gpr : Nat → BitVec 64) (byte : BitVec 64 → BitVec 8) (form : String) : BitVec 64 :=
  if form = "x0+UBFM64[1,63](x1)+24" then gpr 0 + (gpr 1 >>> 1) + 24#64
  else if form = "x0+mem64[x1+8]+24" then gpr 0 + mem64 byte (gpr 1 + 8#64) + 24#64
  else 0#64

/-- The pins of an entry state, from its read view. -/
def pinsOf (gpr : Nat → BitVec 64) (byte : BitVec 64 → BitVec 8) : Pins :=
  ⟨fun i => (gpr i).toNat, fun f => (indirectVA gpr byte f).toNat⟩

def formOK (a : Access) : Bool :=
  match a.2.1 with
  | .indirect f => f == "x0+UBFM64[1,63](x1)+24" || f == "x0+mem64[x1+8]+24"
  | .pin _ _ => true

/-- Every indirect form that occurs in the 14 plans is one of the two handled above. -/
theorem indirect_forms_known :
    (List.range 14).all (fun n => match caseMap n with | some t => t.1.all formOK | none => true) = true := by
  decide

/-- On an indirect access, the data VA is the computed one (Int round trip of a toNat). -/
theorem dataVA_indirect (gpr : Nat → BitVec 64) (byte : BitVec 64 → BitVec 8) (f : String) :
    dataVA (pinsOf gpr byte) (.indirect f) = indirectVA gpr byte f := by
  apply BitVec.eq_of_toNat_eq
  simp [dataVA, baseVA, pinsOf, BitVec.toNat_ofInt]

#print axioms indirect_forms_known
#print axioms dataVA_indirect
end R14E17
