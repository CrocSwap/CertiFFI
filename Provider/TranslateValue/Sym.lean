import TranslateValue.Poly
import TranslateValue.OpNat

/-! ArmCert value layer, normalizer: SSA → polynomials. Each table id t gets a polynomial
P_t over variables = table ids (and quotient variables BIG + t), such that for the ACTUAL table
`vals = evalDefs inputs defs`, (vals t).toNat = eval env P_t with env read off vals (`sym_sound`). Unrecognized
ops fall back to the opaque `var t`, which is trivially sound. Pairing: a `mul [a,b]` uses the value of a
`umulh [a,b]` in the table as its high word; an `add3 [a,b,c]` uses a `carry3 [a,b,c]` when c is a boolean id. -/

set_option autoImplicit false
namespace TranslateValue
open ArmCertValue

/-- Quotient variables live at BIG + t (table ids stay below BIG). -/
def BIG : Nat := 1099511627776

/-- Ops whose value is 0/1 (with their exact arity). -/
def isBoolDef (d : Def) : Bool :=
  match d.op with
  | .carry3 => d.args.length == 3
  | .ovf3 => d.args.length == 3
  | .eqz => d.args.length == 1
  | .msb => d.args.length == 1
  | .cond _ => d.args.length == 4
  | .add3N | .add3Z | .sbc3C | .sbc3V | .sbc3N | .sbc3Z => d.args.length == 3
  | .andN | .andZ => d.args.length == 2
  | .const c => decide (c.toNat ≤ 1)
  | _ => false

def findDef (op : Op) (args : List Arg) : List Def → Nat → Option Nat
  | [], _ => none
  | d :: ds, i => if d.op = op ∧ d.args = args then some i else findDef op args ds (i + 1)

theorem findDef_spec (op : Op) (args : List Arg) : ∀ (defs : List Def) (i j : Nat), findDef op args defs i = some j →
    i ≤ j ∧ defs[j - i]? = some ⟨op, args⟩
  | [], _, _, h => by simp [findDef] at h
  | d :: ds, i, j, h => by
    unfold findDef at h
    split at h
    · next hd =>
      cases h
      refine ⟨Nat.le_refl _, ?_⟩
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq]
      cases d; simp_all
    · obtain ⟨le, get⟩ := findDef_spec op args ds (i + 1) j h
      refine ⟨by omega, ?_⟩
      rw [show j - i = (j - (i + 1)) + 1 by omega]
      simpa using get

def boolId (n : Nat) (defs : List Def) : Arg → Bool
  | .imm c => decide (c.toNat ≤ 1)
  | .id t => if t < n then false else match defs[t - n]? with | some d => isBoolDef d | none => false

/-- The polynomial of an SSA argument, from the prefix table. -/
def argPoly (tbl : List Poly) : Arg → Poly
  | .id a => tbl.getD a (Poly.var a)
  | .imm c => Poly.const c.toNat

/-- One table entry's polynomial, from the prefix table `tbl` (whose length is t). -/
def symDef (n : Nat) (defs : List Def) (tbl : List Poly) (d : Def) : Poly :=
  let t := tbl.length
  let P := argPoly tbl
  let Q := Poly.var (BIG + t)
  let hi := fun (o : Op) (args : List Arg) => match findDef o args defs 0 with
    | some j => Poly.var (n + j) | none => Q
  match d.op with
  | .const c => Poly.const c.toNat
  | .add => match d.args with
    | [a, b] => Poly.sub (Poly.add (P a) (P b)) (Poly.scale pow64 Q) | _ => Poly.var t
  | .sub => match d.args with
    | [a, b] => Poly.add (Poly.sub (P a) (P b)) (Poly.scale pow64 Q) | _ => Poly.var t
  | .not => match d.args with
    | [a] => Poly.sub (Poly.const (pow64 - 1)) (P a) | _ => Poly.var t
  | .lsl k => match d.args with
    | [a] => Poly.sub (Poly.scale (2 ^ k) (P a)) (Poly.scale pow64 Q) | _ => Poly.var t
  | .mul => match d.args with
    | [a, b] => Poly.sub (Poly.mul (P a) (P b)) (Poly.scale pow64 (hi .umulh [a, b])) | _ => Poly.var t
  | .add3 => match d.args with
    | [a, b, c] => Poly.sub (Poly.add (Poly.add (P a) (P b)) (P c))
        (Poly.scale pow64 (if boolId n defs c then hi .carry3 [a, b, c] else Q))
    | _ => Poly.var t
  | .csel => match d.args with
    | [w, a, b] => if boolId n defs w then
        Poly.add (Poly.mul (P w) (P a)) (Poly.mul (Poly.sub (Poly.const 1) (P w)) (P b)) else Poly.var t
    | _ => Poly.var t
  | _ => Poly.var t

def symTable (n : Nat) (defs : List Def) : List Poly :=
  defs.foldl (fun tbl d => tbl ++ [symDef n defs tbl d]) ((List.range n).map Poly.var)

/-- The quotient of a def, from the actual values. -/
def quot (vals : List (BitVec 64)) (d : Def) : Nat :=
  let v := fun (x : Arg) => (Arg.eval vals x).toNat
  match d.op with
  | .add => match d.args with | [a, b] => (v a + v b) / pow64 | _ => 0
  | .sub => match d.args with | [a, b] => if v a < v b then 1 else 0 | _ => 0
  | .lsl k => match d.args with | [a] => (v a * 2 ^ k) / pow64 | _ => 0
  | .mul => match d.args with | [a, b] => (v a * v b) / pow64 | _ => 0
  | .add3 => match d.args with | [a, b, c] => (v a + v b + v c) / pow64 | _ => 0
  | .sbc3 => match d.args with | [a, b, c] => (v a + (pow64 - 1 - v b) + v c) / pow64 | _ => 0
  | .cselc cc => match d.args with
    | [n, z, cf, w, _, _] => if condHolds cc (Arg.eval vals n) (Arg.eval vals z) (Arg.eval vals cf) (Arg.eval vals w) then 1 else 0
    | _ => 0
  | .and => match d.args with
    | [a, .imm m] => if m.toNat + 1 = 2 ^ Nat.log2 (m.toNat + 1) then v a / 2 ^ Nat.log2 (m.toNat + 1) else 0
    | _ => 0
  | .const _ => 0 | .umulh => 0 | .carry3 => 0 | .ovf3 => 0 | .not => 0 | .lsr _ => 0 | .asr _ => 0
  | .orr => 0 | .eor => 0 | .eqz => 0 | .msb => 0 | .cond _ => 0 | .csel => 0 | .add3N => 0 | .add3Z => 0
  | .sbc3C => 0 | .sbc3V => 0 | .sbc3N => 0 | .sbc3Z => 0 | .andN => 0 | .andZ => 0 | .byteAt _ => 0 | .asm8 _ => 0
  | .add32 => 0 | .sub32 => 0 | .sbc3N32 => 0 | .sbc3Z32 => 0 | .sbc3C32 => 0 | .sbc3V32 => 0 | .orrShl _ => 0 | .asm4 _ => 0

def envOf (n : Nat) (defs : List Def) (vals : List (BitVec 64)) : Nat → Int := fun i =>
  if i < BIG then (vals.getD i 0).toNat
  else match defs[i - BIG - n]? with | some d => (quot vals d : Int) | none => 0

/-- SSA well-formedness: every argument is an earlier table id. -/
def WF (n : Nat) (defs : List Def) : Bool :=
  (List.range defs.length).all fun k => match defs[k]? with
    | some d => d.args.all (fun x => match x with | .id i => decide (i < n + k) | .imm _ => true) | none => true

end TranslateValue

namespace TranslateValue
open ArmCertValue
/-- Sanity: x*x as (lo, hi) via mul/umulh: lo + 2^64·hi − x² normalizes to zero. -/
def sqDefs : List Def := [⟨.mul, [.id 0, .id 0]⟩, ⟨.umulh, [.id 0, .id 0]⟩]
theorem sanity_sq :
    Poly.isZero (Poly.sub (Poly.add ((symTable 1 sqDefs).getD 1 []) (Poly.scale pow64 ((symTable 1 sqDefs).getD 2 [])))
      (Poly.mul (Poly.var 0) (Poly.var 0))) = true := by decide +kernel
end TranslateValue
