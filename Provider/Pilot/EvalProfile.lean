import ArmFull
import Pilot.Kern
/-!
# Named concrete CPU/OS profiles

All profile values live in this one file so they can later be filled from hardware probes.

A profile fixes the *configuration* registers to concrete values; everything else (GPRs, PC, NZCV,
SIMD, memory, oracle) stays symbolic. `Holds p s.regs` is the premise a certificate states;
`ovR p` is the overlay that rewrites a register file with the profile values, and `ovR_eq` shows
`Holds p r → ovR p r = r`, which lets the kernel evaluate configuration reads by reduction.
-/
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions

namespace EvalProfile

/-- ARMv8.0-A baseline: only FEAT_AA64EL0..3 implemented (indices 4..7). -/
def featEnabled (i : Nat) : Bool := i == 4 || i == 5 || i == 6 || i == 7
set_option maxRecDepth 100000 in
/-- Explicit list (kernel-reducible by structural recursion; `Vector.ofFn` goes through
well-founded recursion, which the kernel cannot reduce efficiently). -/
def featProfile : Vector Bool 259 :=
  ⟨(List.replicate 4 false ++ List.replicate 4 true ++ List.replicate 251 false).toArray, rfl⟩

set_option maxRecDepth 100000 in
@[simp] theorem featProfile_get (i : Nat) (h : i < 259) : featProfile[i] = featEnabled i := by
  revert i h; decide +kernel

theorem featProfile_get! (i : Nat) (h : i < 259) : featProfile[i]! = featEnabled i := by
  rw [getElem!_pos featProfile i h]; exact featProfile_get i h


/-- Linux arm64 TCR_EL1: T0SZ=T1SZ=16, 4K granules, WBWA inner-shareable walks, IPS=48 bits,
AS=1, TBI0=1, A1=0, no HA/HD. -/
def tcrLinux : BitVec 64 := 0x00000035B5103510#64
/-- Linux arm64 MAIR_EL1 (attr0 Device-nGnRnE, attr1 Device-nGnRE, attr2 Normal-NC, attr3 Normal WB, attr4 Normal tagged). -/
def mairLinux : BitVec 64 := 0x000000F0FF440400#64
/-- Linux INIT_SCTLR_EL1_MMU_ON for a v8.0 CPU, little endian, PAC keys disabled:
M C SA SA0 SED EOS I DZE UCT nTWE TSCXT IESB EIS SPAN UCI nTLSMD LSMAOE. -/
def sctlrLinux : BitVec 64 := 0x34F4D91D#64
/-- Same with M = 0 (stage-1 MMU off). -/
def sctlrOff : BitVec 64 := 0x34F4D91C#64
/-- Non-VHE host / EL2 idle: HCR_EL2 = RW only (E2H=TGE=VM=DC=0, no traps). -/
def hcrNvhe : BitVec 64 := 0x80000000#64
/-- SCR_EL3: NS=1, RES1 bits 4,5, HCE=1, RW=1. -/
def scrEl3 : BitVec 64 := 0x531#64
/-- Implemented PA size (`__supported_pa_size`, read by `AArch64_PAMax`): 48 bits. -/
def paSize : Int := 48
/-- EDSCR: STATUS = 0b000010 (non-debug), HDE = 0. -/
def edscr0 : BitVec 32 := 0x2#32

structure Profile where
  feat : Vector Bool 259
  r64 : List (Bank_BitVec_64 × BitVec 64)
  r32 : List (Bank_BitVec_32 × BitVec 32)
  rBool : List (Bank_Bool × Bool)
  rInt : List (Bank_Int × Int)
  el : BitVec 2

def ovMap {κ α : Type} [DecidableEq κ] (l : List (κ × α)) (f : RegMap κ α) : RegMap κ α :=
  l.foldr (fun kv g => RegMap.set g kv.1 kv.2) f

def ovR (p : Profile) (r : Regs) : Regs :=
  { r with FeatureImpl := p.feat,
           bank_BitVec_64 := ovMap p.r64 r.bank_BitVec_64,
           bank_BitVec_32 := ovMap p.r32 r.bank_BitVec_32,
           bank_Bool := ovMap p.rBool r.bank_Bool,
           bank_Int := ovMap p.rInt r.bank_Int,
           PSTATE := { r.PSTATE with EL := p.el, nRW := 0#1 } }

/-- The premise: the register file agrees with the profile on every configuration register. -/
def Holds (p : Profile) (r : Regs) : Prop :=
  r.FeatureImpl = p.feat ∧ (∀ kv ∈ p.r64, r.bank_BitVec_64 kv.1 = kv.2) ∧
  (∀ kv ∈ p.r32, r.bank_BitVec_32 kv.1 = kv.2) ∧ (∀ kv ∈ p.rBool, r.bank_Bool kv.1 = kv.2) ∧
  (∀ kv ∈ p.rInt, r.bank_Int kv.1 = kv.2) ∧
  r.PSTATE.EL = p.el ∧ r.PSTATE.nRW = 0#1

theorem set_self {κ α : Type} [DecidableEq κ] (f : RegMap κ α) (k : κ) (v : α) (h : f k = v) :
    RegMap.set f k v = f := by
  funext k'; unfold RegMap.set; split
  · rename_i heq; rw [heq, h]
  · rfl

theorem ovMap_eq {κ α : Type} [DecidableEq κ] (l : List (κ × α)) (f : RegMap κ α)
    (h : ∀ kv ∈ l, f kv.1 = kv.2) : ovMap l f = f := by
  induction l with
  | nil => rfl
  | cons kv l ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    show RegMap.set (ovMap l f) kv.1 kv.2 = f
    rw [ih']; exact set_self f kv.1 kv.2 (h kv List.mem_cons_self)

theorem ovR_eq {p : Profile} {r : Regs} (h : Holds p r) : ovR p r = r := by
  obtain ⟨hf, h64, h32, hb, hi, hel, hnrw⟩ := h
  unfold ovR
  rw [ovMap_eq _ _ h64, ovMap_eq _ _ h32, ovMap_eq _ _ hb, ovMap_eq _ _ hi, ← hf, ← hel, ← hnrw]

def sOv (p : Profile) (s : SequentialState Regs oracleChoiceSource) : SequentialState Regs oracleChoiceSource :=
  { s with regs := ovR p s.regs }

theorem sOv_eq {p : Profile} {s : SequentialState Regs oracleChoiceSource} (h : Holds p s.regs) :
    sOv p s = s := by
  unfold sOv; rw [ovR_eq h]

/-- Shared configuration registers of the Linux EL0 profiles (non-VHE EL1&0, family 3). -/
def cfg64 (sctlr : BitVec 64) : List (Bank_BitVec_64 × BitVec 64) :=
  [(.SCTLR_EL1, sctlr), (.TCR_EL1, tcrLinux), (.MAIR_EL1, mairLinux), (.HCR_EL2, hcrNvhe),
   (.SCR_EL3, scrEl3), (.MDSCR_EL1, 0#64), (.MPAM2_EL2, 0#64), (._MPAM3_EL3, 0#64)]

/-- Profile `pilot-v8.0-EL10-mmuoff`: Linux EL0 user mode, v8.0 baseline, non-VHE EL1&0, stage-1 MMU disabled. -/
def profOff : Profile where
  feat := featProfile
  r64 := cfg64 sctlrOff
  r32 := [(._EDSCR, edscr0)]
  rBool := [(.SPESampleInFlight, false)]
  rInt := [(.__supported_pa_size, paSize)]
  el := 0#2

/-- Profile `pilot-v8.0-EL10` (family 3): Linux EL0, v8.0, non-VHE EL1&0, stage-1 MMU on, stage 2 off. -/
def profLinux : Profile where
  feat := featProfile
  r64 := cfg64 sctlrLinux
  r32 := [(._EDSCR, edscr0)]
  rBool := [(.SPESampleInFlight, false)]
  rInt := [(.__supported_pa_size, paSize)]
  el := 0#2

end EvalProfile
