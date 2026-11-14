-- ArmCert VALUE LAYER, interface v0 (certiffi). ArmCert-only: imports ArmFull
-- via RegBindCore; no ArmState / LNSym / bridges.
--
-- Design: an SSA value table threaded along the Sail run.
--   * `Op` / `Def` / `evalDefs`: a straight-line SSA program over BitVec 64 (flags are 0/1 words).
--   * `Sym`: where each tracked location (GPR/SP, NZCV, typed region words) lives in the table.
--   * `Agrees`: the actual Sail state matches the table at those locations.
-- * Per-class value effects are `VHolds us fl x y` over SOURCE-state reads; memory classes
--     (Memory) are `MemVHolds`. certiffi proves once that a step with those facts extends the table
--     (`compile`) and preserves `Agrees`; the run theorem folds that over the plan.
-- * Per kernel: one math lemma about `evalDefs inputs defs` at the output ids (normalizer).
import HeapV2StepCerts.RegBindCore
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
namespace ArmCertValue
open HeapV2StepCerts.RegBind (Reg St regVal)

/-- SSA operations. Every value is a BitVec 64; flag values are the words 0 / 1. -/
inductive Op where
  | const (c : BitVec 64)
  | add | sub | mul | umulh
  | add3            -- a + b + c                      (ADC/ADCS/SBC/SBCS/SUBS with `not`)
  | carry3          -- carry out of a + b + c (0/1)
  | ovf3            -- signed overflow of a + b + c (0/1)
  | not
  | lsl (n : Nat) | lsr (n : Nat) | asr (n : Nat)
  | and | orr | eor
  | eqz             -- 1 if a = 0 else 0               (Z)
  | msb             -- bit 63 as 0/1                   (N)
  | cond (c : BitVec 4)  -- args [n, z, c, v]: ConditionHolds c as 0/1
  | csel            -- args [w, a, b]: if w ≠ 0 then a else b
  -- flag-setting arithmetic, one op per result (args [a, b, c]; c = carry-in word 0/1):
  | add3N | add3Z    -- N / Z of a + b + c                  (ADDS/ADCS; carry3/ovf3 give C/V)
  | sbc3             -- a + ~b + c                          (SUBS: c = 1, SBC(S): c = C)
  | sbc3C | sbc3V | sbc3N | sbc3Z  -- flags of a + ~b + c
  | andN | andZ      -- N / Z of a &&& b                    (ANDS/TST; C = V = 0)
  | cselc (c : BitVec 4)  -- args [n, z, c, v, a, b]: if ConditionHolds c then a else b
  -- byte <-> word (memory regions are tracked per byte):
  | byteAt (k : Nat)      -- args [a]: (a >>> 8k) &&& 0xff
  | asm8 (ks : List Nat)  -- args [a0..a7], ks = [k0..k7]: Σ_i ((a_i >>> 8 k_i) &&& 0xff) <<< 8i
  -- Core v5 (additive, runtime14):
  | add32 | sub32         -- W-register ADD/SUB: low 32 bits, zero-extended
  | sbc3N32 | sbc3Z32 | sbc3C32 | sbc3V32  -- flags of the 32-bit a + ~b + c (low halves)
  | orrShl (n : Nat)      -- args [a, b]: a ||| (b <<< n)
  | asm4 (ks : List Nat)  -- args [a0..a3]: Σ_{i<4} ((a_i >>> 8 k_i) &&& 0xff) <<< 8i
  deriving DecidableEq, Repr

def b01 (b : Bool) : BitVec 64 := if b then 1#64 else 0#64

/-- Byte k of a, zero-extended, placed at byte position i. -/
def bytePart (a : BitVec 64) (k i : Nat) : BitVec 64 := ((a >>> (8 * k)) &&& 0xff#64) <<< (8 * i)

/-- Arm condition codes over N/Z/C/V words (nonzero = set). -/
def condHolds (c : BitVec 4) (n z cf v : BitVec 64) : Bool :=
  let N := n != 0; let Z := z != 0; let C := cf != 0; let V := v != 0
  let base := match c.toNat / 2 with
    | 0 => Z | 1 => C | 2 => N | 3 => V | 4 => C && !Z | 5 => N == V | 6 => (N == V) && !Z | _ => true
  if c.toNat % 2 = 1 && c.toNat != 15 then !base else base

def Op.eval : Op → List (BitVec 64) → BitVec 64
  | .const c, _ => c
  | .add, [a, b] => a + b
  | .sub, [a, b] => a - b
  | .mul, [a, b] => a * b
  | .umulh, [a, b] => BitVec.ofNat 64 ((a.toNat * b.toNat) / 2 ^ 64)
  | .add3, [a, b, c] => a + b + c
  | .carry3, [a, b, c] => b01 (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)
  | .ovf3, [a, b, c] => b01 (decide (a.toInt + b.toInt + c.toNat < -2 ^ 63 ∨ 2 ^ 63 ≤ a.toInt + b.toInt + c.toNat))
  | .not, [a] => ~~~a
  | .lsl n, [a] => a <<< n
  | .lsr n, [a] => a >>> n
  | .asr n, [a] => a.sshiftRight n
  | .and, [a, b] => a &&& b
  | .orr, [a, b] => a ||| b
  | .eor, [a, b] => a ^^^ b
  | .eqz, [a] => b01 (a == 0)
  | .msb, [a] => b01 a.msb
  | .cond c, [n, z, cf, v] => b01 (condHolds c n z cf v)
  | .csel, [w, a, b] => if w ≠ 0 then a else b
  | .add3N, [a, b, c] => b01 (a + b + c).msb
  | .add3Z, [a, b, c] => b01 (a + b + c == 0)
  | .sbc3, [a, b, c] => a + ~~~b + c
  | .sbc3C, [a, b, c] => b01 (2 ^ 64 ≤ a.toNat + (~~~b).toNat + c.toNat)
  | .sbc3V, [a, b, c] => b01 (decide (a.toInt + (~~~b).toInt + c.toNat < -2 ^ 63 ∨ 2 ^ 63 ≤ a.toInt + (~~~b).toInt + c.toNat))
  | .sbc3N, [a, b, c] => b01 (a + ~~~b + c).msb
  | .sbc3Z, [a, b, c] => b01 (a + ~~~b + c == 0)
  | .andN, [a, b] => b01 (a &&& b).msb
  | .andZ, [a, b] => b01 (a &&& b == 0)
  | .cselc c, [n, z, cf, v, a, b] => if condHolds c n z cf v then a else b
  | .byteAt k, [a] => (a >>> (8 * k)) &&& 0xff#64
  | .asm8 [k0, k1, k2, k3, k4, k5, k6, k7], [a0, a1, a2, a3, a4, a5, a6, a7] =>
      bytePart a0 k0 0 + bytePart a1 k1 1 + bytePart a2 k2 2 + bytePart a3 k3 3 +
      bytePart a4 k4 4 + bytePart a5 k5 5 + bytePart a6 k6 6 + bytePart a7 k7 7
  | .add32, [a, b] => ((a + b).setWidth 32).setWidth 64
  | .sub32, [a, b] => ((a - b).setWidth 32).setWidth 64
  | .sbc3N32, [a, b, c] => b01 (a.setWidth 32 + ~~~(b.setWidth 32) + c.setWidth 32).msb
  | .sbc3Z32, [a, b, c] => b01 (a.setWidth 32 + ~~~(b.setWidth 32) + c.setWidth 32 == 0)
  | .sbc3C32, [a, b, c] => b01 (2 ^ 32 ≤ (a.setWidth 32).toNat + (~~~(b.setWidth 32)).toNat + (c.setWidth 32).toNat)
  | .sbc3V32, [a, b, c] => b01 (decide ((a.setWidth 32).toInt + (~~~(b.setWidth 32)).toInt + (c.setWidth 32).toNat < -2 ^ 31 ∨
      2 ^ 31 ≤ (a.setWidth 32).toInt + (~~~(b.setWidth 32)).toInt + (c.setWidth 32).toNat))
  | .orrShl n, [a, b] => a ||| (b <<< n)
  | .asm4 [k0, k1, k2, k3], [a0, a1, a2, a3] =>
      bytePart a0 k0 0 + bytePart a1 k1 1 + bytePart a2 k2 2 + bytePart a3 k3 3
  | _, _ => 0#64

/-- An SSA argument: an earlier table entry or an immediate. -/
inductive Arg where
  | id (n : Nat)
  | imm (c : BitVec 64)
  deriving DecidableEq, Repr

def Arg.eval (vals : List (BitVec 64)) : Arg → BitVec 64
  | .id n => vals.getD n 0
  | .imm c => c

/-- One SSA definition: `op` applied to earlier table entries / immediates (inputs first). -/
structure Def where
  op : Op
  args : List Arg
  deriving DecidableEq, Repr

def Def.eval (vals : List (BitVec 64)) (d : Def) : BitVec 64 := d.op.eval (d.args.map (Arg.eval vals))

/-- Append the values of `defs` to the table `vals`, in order. -/
def extend (vals : List (BitVec 64)) (defs : List Def) : List (BitVec 64) :=
  defs.foldl (fun vals d => vals ++ [d.eval vals]) vals

/-- The value table: the inputs, then one entry per definition, in order. -/
def evalDefs (inputs : List (BitVec 64)) (defs : List Def) : List (BitVec 64) := extend inputs defs

/-- A typed memory region of 64-bit little-endian words at VA = pin + off (Memory refines). -/
structure Region where
  pin : Nat
  off : Int
  words : Nat
  deriving DecidableEq, Repr

/-- Word i of region r in state s, read through the deployment mapping (Memory owns this definition). -/
def regionWord (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (s : St) (r : Region) (i : Nat) :
    Option (BitVec 64) :=
  let va : Int := (pinv r.pin : Int) + r.off + 8 * i
  (List.range 8).foldr (fun j acc => do
      let pa ← mapping (BitVec.ofInt 64 (va + j))
      let byte ← s.mem[pa]?
      let rest ← acc
      pure (rest ||| ((byte.setWidth 64) <<< (8 * j)))) (some 0#64)

/-- Byte j of region r in state s (va = pin + off + j), through the mapping (Memory may refine the body). -/
def regionByte (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (s : St) (r : Region) (j : Nat) :
    Option (BitVec 8) :=
  (mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + j))).bind fun pa => s.mem[pa]?

/-- Symbolic state: table ids of the tracked locations (`none` = untracked). Memory is tracked per byte:
`memB r j = some (i, k)` means byte j of region r is byte k of table entry i. -/
structure Sym where
  regs : Reg → Option Nat
  nzcv : Option (Nat × Nat × Nat × Nat)
  memB : Region → Nat → Option (Nat × Nat)

/-- The actual state agrees with the value table on every tracked location. -/
def Agrees (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (vals : List (BitVec 64)) (σ : Sym)
    (s : St) : Prop :=
  (∀ r i, σ.regs r = some i → regVal s r = vals.getD i 0) ∧
  (∀ n z c v, σ.nzcv = some (n, z, c, v) →
    s.regs.PSTATE.N.setWidth 64 = vals.getD n 0 ∧ s.regs.PSTATE.Z.setWidth 64 = vals.getD z 0 ∧
    s.regs.PSTATE.C.setWidth 64 = vals.getD c 0 ∧ s.regs.PSTATE.V.setWidth 64 = vals.getD v 0) ∧
  (∀ r j i k, σ.memB r j = some (i, k) →
    regionByte mapping pinv s r j = some (((vals.getD i 0) >>> (8 * k)).setWidth 8))

/-- Every tracked id is below n (the current table length). -/
def Sym.Bounded (σ : Sym) (n : Nat) : Prop :=
  (∀ r i, σ.regs r = some i → i < n) ∧
  (∀ a b c d, σ.nzcv = some (a, b, c, d) → a < n ∧ b < n ∧ c < n ∧ d < n) ∧
  (∀ r j i k, σ.memB r j = some (i, k) → i < n)

/-! ## Per-class value effects (generator target) -/

/-- A value source read in the step's SOURCE state. -/
inductive Src where
  | reg (r : Reg)
  | flag (i : Fin 4)     -- 0 N, 1 Z, 2 C, 3 V (as 0/1 words)
  | lit (c : BitVec 64)
  deriving DecidableEq, Repr

def flagWord (s : St) : Fin 4 → BitVec 64
  | 0 => s.regs.PSTATE.N.setWidth 64
  | 1 => s.regs.PSTATE.Z.setWidth 64
  | 2 => s.regs.PSTATE.C.setWidth 64
  | 3 => s.regs.PSTATE.V.setWidth 64

def srcVal (s : St) : Src → BitVec 64
  | .reg r => regVal s r
  | .flag i => flagWord s i
  | .lit c => c

/-- A register or flag update: op applied to source reads. -/
structure VUpd where
  op : Op
  args : List Src
  deriving DecidableEq, Repr

def VUpd.eval (s : St) (u : VUpd) : BitVec 64 := u.op.eval (u.args.map (srcVal s))

/-- The step's GPR/SP value effect. `some u`: written with u's value; `none`: clobbered (untracked
afterwards); unlisted: unchanged. Flags: `none` = NZCV unchanged, `some fs` = new NZCV words. -/
def VHolds (us : List (Reg × Option VUpd)) (fl : Option (VUpd × VUpd × VUpd × VUpd)) (x y : St) : Prop :=
  (∀ r, match (us.find? (·.1 = r)).map (·.2) with
    | none => regVal y r = regVal x r
    | some none => True
    | some (some u) => regVal y r = u.eval x) ∧
  (match fl with
    | none => ∀ i, flagWord y i = flagWord x i
    | some (n, z, c, v) => flagWord y 0 = n.eval x ∧ flagWord y 1 = z.eval x ∧
        flagWord y 2 = c.eval x ∧ flagWord y 3 = v.eval x)

/-! ## Memory-class value effects (Memory's target; shape fixed here, semantics Memory's) -/

inductive MemEff where
  | load (rt : Reg) (r : Region) (i : Nat)     -- 64-bit load of word i into rt
  | store (rt : Reg) (r : Region) (i : Nat)    -- 64-bit store of rt into word i
  | loadb (rt : Reg) (r : Region) (j : Nat)    -- LDRB: rt := zero-extended byte j
  | storeb (rt : Reg) (r : Region) (j : Nat)   -- STRB: byte j := low byte of rt
  | load32 (rt : Reg) (r : Region) (j : Nat)   -- LDR Wt: rt := zero-extended LE bytes j..j+3 (v5)
  | store32 (rt : Reg) (r : Region) (j : Nat)  -- STR Wt: bytes j..j+3 := low 32 bits of rt (v5)
  deriving DecidableEq, Repr

/-- Loads/stores of the step against the region model, plus word- and byte-granular frames over the
declared regions: every word / byte not written by this step is unchanged. -/
def MemVHolds (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region)
    (effs : List MemEff) (x y : St) : Prop :=
  (∀ e ∈ effs, match e with
    | .load rt r i => regionWord mapping pinv x r i = some (regVal y rt)
    | .store rt r i => regionWord mapping pinv y r i = some (regVal x rt)
    | .loadb rt r j => ∃ b, regionByte mapping pinv x r j = some b ∧ regVal y rt = b.setWidth 64
    | .storeb rt r j => regionByte mapping pinv y r j = some ((regVal x rt).setWidth 8)
    | .load32 rt r j => ∃ u : BitVec 64, u.toNat < 2 ^ 32 ∧
        (∀ t, t < 4 → regionByte mapping pinv x r (j + t) = some ((u >>> (8 * t)).setWidth 8)) ∧ regVal y rt = u
    | .store32 rt r j => ∀ t, t < 4 → regionByte mapping pinv y r (j + t) = some ((regVal x rt >>> (8 * t)).setWidth 8)) ∧
  (∀ r ∈ regions, ∀ w, w < r.words → (∀ rt, MemEff.store rt r w ∉ effs) →
    (∀ rt j, MemEff.storeb rt r j ∈ effs → j / 8 ≠ w) →
    (∀ rt j', MemEff.store32 rt r j' ∈ effs → j' + 4 ≤ 8 * w ∨ 8 * w + 8 ≤ j') →
    regionWord mapping pinv y r w = regionWord mapping pinv x r w) ∧
  (∀ r ∈ regions, ∀ j, j < 8 * r.words → (∀ rt, MemEff.storeb rt r j ∉ effs) →
    (∀ rt, MemEff.store rt r (j / 8) ∉ effs) →
    (∀ rt j', MemEff.store32 rt r j' ∈ effs → ¬ (j' ≤ j ∧ j < j' + 4)) →
    regionByte mapping pinv y r j = regionByte mapping pinv x r j)

/-! ## One plan step (generated per program) -/

structure StepV where
  us : List (Reg × Option VUpd)
  fl : Option (VUpd × VUpd × VUpd × VUpd)
  mem : List MemEff

end ArmCertValue
