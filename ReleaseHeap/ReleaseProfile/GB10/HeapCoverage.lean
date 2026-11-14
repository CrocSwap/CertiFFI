import ArmCertTranslateModel.HeapV2Plan
import ArmCertTranslateModel.HeapV2ShimPlan
import HeapV2StepCerts.CodeScope

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Heap full executable coverage

Every byte of the RX PT_LOAD of the reviewed ELF `heap-v2-d163.elf`
(sha256 032b5400a41bc1da9f7c66a2eb4f53ae71a8aeb0591918d64a2b627d966fd603) is classified. The segment is
file [0x278, 0x574), vaddr = file + 0x10000, link base 0. Words are read from the ELF bytes themselves
(`HeapV2.file`): the plans' word lists are tied to the bytes by their `codeWords_bytes`, and the trap and
harness words by the byte theorems here. The classes are:

* **covered**: `HeapV2Plan.codeWords` at file 0x278 (body, memcpy, memset, bignum_sqr_p256k1_alt) and
  `HeapV2ShimPlan.codeWords` at file 0x548 (the certified entry `certiffi_heapv2_shim`);
* **trap stop word**: `certiffi_trap` at file 0x544, `brk #0` (0xd4200000). This is the Breakpoint exception
  that the trap cards end in. It is reviewed here by a byte theorem;
* **unreachable**: `__wrap_memmove`/`certiffi_memmove` at file [0x3bc, 0x3f0). `covered_closed` shows the
  covered set plus the trap is closed under every successor of a covered word: direct-branch targets
  (B/BL/B.cond/CBZ/CBNZ/TBZ/TBNZ) and fall-through. No covered word is BR/BLR/ERET or another register branch
  except RET, and no covered word is exception-generating. Hence, from the entry 0x548, execution stays in
  covered ∪ {trap} until a RET leaves through the link register to the caller. The memmove range is disjoint
  from that set;
* **caller harness**: `_start` at file [0x33c, 0x3a0), 25 words, byte-pinned below. **PROVISIONAL class
 CALLER_HARNESS, pending the release owner.** It is the ELF entry/smoke driver (d163 CertifiedStartShim.S, "outside
  certified entry scope"). It runs before the window (frame setup, `bl certiffi_heapv2_shim`) and after the
  shim's RET (result check, `svc #0` exit, x8 = 93). It is not reachable from the certified entry.
-/

namespace ReleaseProfile.GB10.HeapCoverage

open ArmCert.Translate.Model

/-- File offset of `certiffi_trap` (vaddr 0x10544). -/
def trapOffset : Nat := 0x544
/-- `brk #0`. -/
def trapWord : Nat := 0xd4200000
/-- Certified entry `certiffi_heapv2_shim` (vaddr 0x10548). -/
def entryOffset : Nat := 0x548

/-- All reviewed code words as (file offset, word): body plan at 0x278, shim plan at 0x548. -/
def coveredWords : List (Nat × Nat) :=
  HeapV2Plan.codeWords.map (fun c => (0x278 + c.1, c.2)) ++ HeapV2ShimPlan.codeWords.map (fun c => (0x548 + c.1, c.2))

def coveredOffsets : List Nat := coveredWords.map (·.1)

/-- The covered words ARE the ELF bytes (from the plans' kernel-decided `codeWords_bytes`). -/
theorem coveredWords_bytes : ∀ c ∈ coveredWords, ∀ i < 4,
    HeapV2.file (c.1 + i) = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) := by
  intro c hc i hi
  simp only [coveredWords, List.mem_append, List.mem_map] at hc
  rcases hc with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
  · simpa [Nat.add_assoc] using HeapV2Plan.codeWords_bytes d hd i hi
  · simpa [Nat.add_assoc] using HeapV2ShimPlan.codeWords_bytes d hd i hi

/-- Two's-complement sign extension of a `bits`-wide immediate. -/
def sext (v bits : Nat) : Int := if v ≥ 2 ^ (bits - 1) then (v : Int) - (2 ^ bits : Nat) else (v : Int)

/-- Direct (PC-relative immediate) branch target of word `w` at offset `o`, if `w` is B/BL, B.cond or
FEAT_HBC BC.cond (0x54 class, bit 4 either value), CBZ/CBNZ or TBZ/TBNZ. -/
def directTarget (o w : Nat) : Option Int :=
  if w &&& 0x7C000000 == 0x14000000 then some ((o : Int) + 4 * sext (w &&& 0x3FFFFFF) 26)
  else if w &&& 0xFF000000 == 0x54000000 then some ((o : Int) + 4 * sext ((w >>> 5) &&& 0x7FFFF) 19)
  else if w &&& 0x7E000000 == 0x34000000 then some ((o : Int) + 4 * sext ((w >>> 5) &&& 0x7FFFF) 19)
  else if w &&& 0x7E000000 == 0x36000000 then some ((o : Int) + 4 * sext ((w >>> 5) &&& 0x3FFF) 14)
  else none

/-- Unconditional branch (register) class: BR, BLR, RET, ERET, DRPS and their PAC forms. -/
def isRegBranch (w : Nat) : Bool := w &&& 0xFE000000 == 0xD6000000
/-- Plain `RET Xn`. -/
def isRet (w : Nat) : Bool := w &&& 0xFFFFFC1F == 0xD65F0000
/-- Exception generation (SVC/HVC/SMC/BRK/HLT/DCPS). -/
def isExcGen (w : Nat) : Bool := w &&& 0xFF000000 == 0xD4000000
/-- Unconditional immediate `B` (no fall-through). -/
def isB (w : Nat) : Bool := w &&& 0xFC000000 == 0x14000000

/-- Membership in covered ∪ {trap}. -/
def inScope (t : Int) : Bool := t == (trapOffset : Int) || coveredOffsets.any (fun c => (c : Int) == t)

/-- Every successor of the word `w` at `o` is in scope. The only exit is RET; there is no other indirect
branch and no exception generation. -/
def wordOk (o w : Nat) : Bool :=
  (!isRegBranch w || isRet w) && !isExcGen w &&
  (match directTarget o w with | some t => inScope t | none => true) &&
  (isB w || isRet w || inScope ((o : Int) + 4))

/-- (1) The trap stop word: the ELF bytes at file 0x544 are `brk #0`. -/
theorem trap_bytes : ∀ i < 4,
    HeapV2.file (trapOffset + i) = some ((BitVec.ofNat 32 trapWord).extractLsb' (8 * i) 8) := by
  decide +kernel

/-- The trap word is exception-generating (a stop), and it is not a covered word. -/
theorem trap_stop : isExcGen trapWord = true ∧ trapOffset ∉ coveredOffsets := by decide +kernel

/-- The certified entry is covered. -/
theorem entry_covered : entryOffset ∈ coveredOffsets := by decide +kernel

/-- (2) The covered set plus the trap is closed under all successors of covered words. The words are the ELF
bytes by `coveredWords_bytes`. -/
theorem covered_closed : coveredWords.all (fun c => wordOk c.1 c.2) = true := by decide +kernel

theorem covered_closed_prop : ∀ c ∈ coveredWords, wordOk c.1 c.2 = true :=
  fun c h => List.all_eq_true.1 covered_closed c h

/-- memmove [0x3bc, 0x3f0) is disjoint from covered ∪ {trap}, so it is unreachable from the entry. -/
theorem memmove_disjoint :
    coveredOffsets.all (fun o => !(Nat.ble 0x3bc o && Nat.blt o 0x3f0)) = true ∧
    !(Nat.ble 0x3bc trapOffset && Nat.blt trapOffset 0x3f0) = true := by
  decide +kernel

/-- (3) PROVISIONAL CALLER_theorem harnessBytes_0 : ∀ i < 4, HeapV2.file (0x33c + 0x0 + i) = some ((BitVec.ofNat 32 0xd10103ff).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_1 : ∀ i < 4, HeapV2.file (0x33c + 0x4 + i) = some ((BitVec.ofNat 32 0xa9007fff).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_2 : ∀ i < 4, HeapV2.file (0x33c + 0x8 + i) = some ((BitVec.ofNat 32 0xa9017fff).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_3 : ∀ i < 4, HeapV2.file (0x33c + 0xc + i) = some ((BitVec.ofNat 32 0xd2800049).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_4 : ∀ i < 4, HeapV2.file (0x33c + 0x10 + i) = some ((BitVec.ofNat 32 0xf90003e9).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_5 : ∀ i < 4, HeapV2.file (0x33c + 0x14 + i) = some ((BitVec.ofNat 32 0x910003e1).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_6 : ∀ i < 4, HeapV2.file (0x33c + 0x18 + i) = some ((BitVec.ofNat 32 0x910083e0).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_7 : ∀ i < 4, HeapV2.file (0x33c + 0x1c + i) = some ((BitVec.ofNat 32 0xd2800402).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_8 : ∀ i < 4, HeapV2.file (0x33c + 0x20 + i) = some ((BitVec.ofNat 32 0xd2800403).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_9 : ∀ i < 4, HeapV2.file (0x33c + 0x24 + i) = some ((BitVec.ofNat 32 0x9400007a).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_10 : ∀ i < 4, HeapV2.file (0x33c + 0x28 + i) = some ((BitVec.ofNat 32 0xb5000180).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_11 : ∀ i < 4, HeapV2.file (0x33c + 0x2c + i) = some ((BitVec.ofNat 32 0xf94013e9).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_12 : ∀ i < 4, HeapV2.file (0x33c + 0x30 + i) = some ((BitVec.ofNat 32 0xf100113f).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_13 : ∀ i < 4, HeapV2.file (0x33c + 0x34 + i) = some ((BitVec.ofNat 32 0x54000121).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_14 : ∀ i < 4, HeapV2.file (0x33c + 0x38 + i) = some ((BitVec.ofNat 32 0xf94017e9).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_15 : ∀ i < 4, HeapV2.file (0x33c + 0x3c + i) = some ((BitVec.ofNat 32 0xf9401bea).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_16 : ∀ i < 4, HeapV2.file (0x33c + 0x40 + i) = some ((BitVec.ofNat 32 0xf9401feb).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_17 : ∀ i < 4, HeapV2.file (0x33c + 0x44 + i) = some ((BitVec.ofNat 32 0xaa0a0129).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_18 : ∀ i < 4, HeapV2.file (0x33c + 0x48 + i) = some ((BitVec.ofNat 32 0xaa0b0129).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_19 : ∀ i < 4, HeapV2.file (0x33c + 0x4c + i) = some ((BitVec.ofNat 32 0xb5000069).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_20 : ∀ i < 4, HeapV2.file (0x33c + 0x50 + i) = some ((BitVec.ofNat 32 0xd2800000).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_21 : ∀ i < 4, HeapV2.file (0x33c + 0x54 + i) = some ((BitVec.ofNat 32 0x14000002).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_22 : ∀ i < 4, HeapV2.file (0x33c + 0x58 + i) = some ((BitVec.ofNat 32 0xd2800020).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_23 : ∀ i < 4, HeapV2.file (0x33c + 0x5c + i) = some ((BitVec.ofNat 32 0xd2800ba8).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_24: ∀ i < 4, HeapV2.file (0x33c + 0x60 + i) = some ((BitVec.ofNat 32 0xd4000001).extractLsb' (8 * i) 8):= by decide +kernel: `_start`, 25 words at file 0x33c, each byte-pinned to the
ELF. -/
theorem harnessBytes_0 : ∀ i < 4, HeapV2.file (0x33c + 0x0 + i) = some ((BitVec.ofNat 32 0xd10103ff).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_1 : ∀ i < 4, HeapV2.file (0x33c + 0x4 + i) = some ((BitVec.ofNat 32 0xa9007fff).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_2 : ∀ i < 4, HeapV2.file (0x33c + 0x8 + i) = some ((BitVec.ofNat 32 0xa9017fff).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_3 : ∀ i < 4, HeapV2.file (0x33c + 0xc + i) = some ((BitVec.ofNat 32 0xd2800049).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_4 : ∀ i < 4, HeapV2.file (0x33c + 0x10 + i) = some ((BitVec.ofNat 32 0xf90003e9).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_5 : ∀ i < 4, HeapV2.file (0x33c + 0x14 + i) = some ((BitVec.ofNat 32 0x910003e1).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_6 : ∀ i < 4, HeapV2.file (0x33c + 0x18 + i) = some ((BitVec.ofNat 32 0x910083e0).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_7 : ∀ i < 4, HeapV2.file (0x33c + 0x1c + i) = some ((BitVec.ofNat 32 0xd2800402).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_8 : ∀ i < 4, HeapV2.file (0x33c + 0x20 + i) = some ((BitVec.ofNat 32 0xd2800403).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_9 : ∀ i < 4, HeapV2.file (0x33c + 0x24 + i) = some ((BitVec.ofNat 32 0x9400007a).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_10 : ∀ i < 4, HeapV2.file (0x33c + 0x28 + i) = some ((BitVec.ofNat 32 0xb5000180).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_11 : ∀ i < 4, HeapV2.file (0x33c + 0x2c + i) = some ((BitVec.ofNat 32 0xf94013e9).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_12 : ∀ i < 4, HeapV2.file (0x33c + 0x30 + i) = some ((BitVec.ofNat 32 0xf100113f).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_13 : ∀ i < 4, HeapV2.file (0x33c + 0x34 + i) = some ((BitVec.ofNat 32 0x54000121).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_14 : ∀ i < 4, HeapV2.file (0x33c + 0x38 + i) = some ((BitVec.ofNat 32 0xf94017e9).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_15 : ∀ i < 4, HeapV2.file (0x33c + 0x3c + i) = some ((BitVec.ofNat 32 0xf9401bea).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_16 : ∀ i < 4, HeapV2.file (0x33c + 0x40 + i) = some ((BitVec.ofNat 32 0xf9401feb).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_17 : ∀ i < 4, HeapV2.file (0x33c + 0x44 + i) = some ((BitVec.ofNat 32 0xaa0a0129).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_18 : ∀ i < 4, HeapV2.file (0x33c + 0x48 + i) = some ((BitVec.ofNat 32 0xaa0b0129).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_19 : ∀ i < 4, HeapV2.file (0x33c + 0x4c + i) = some ((BitVec.ofNat 32 0xb5000069).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_20 : ∀ i < 4, HeapV2.file (0x33c + 0x50 + i) = some ((BitVec.ofNat 32 0xd2800000).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_21 : ∀ i < 4, HeapV2.file (0x33c + 0x54 + i) = some ((BitVec.ofNat 32 0x14000002).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_22 : ∀ i < 4, HeapV2.file (0x33c + 0x58 + i) = some ((BitVec.ofNat 32 0xd2800020).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_23 : ∀ i < 4, HeapV2.file (0x33c + 0x5c + i) = some ((BitVec.ofNat 32 0xd2800ba8).extractLsb' (8 * i) 8) := by decide +kernel
theorem harnessBytes_24 : ∀ i < 4, HeapV2.file (0x33c + 0x60 + i) = some ((BitVec.ofNat 32 0xd4000001).extractLsb' (8 * i) 8) := by decide +kernel

/-- Every word of the RX segment [0x278, 0x574) is covered, the trap, the caller harness [0x33c, 0x3a0) or
unreachable memmove [0x3bc, 0x3f0). The classes cover all 191 words. -/
theorem rx_partition : (List.range 191).all (fun k =>
    coveredOffsets.contains (0x278 + 4 * k) || 0x278 + 4 * k == trapOffset ||
    (Nat.ble 0x33c (0x278 + 4 * k) && Nat.blt (0x278 + 4 * k) 0x3a0) ||
    (Nat.ble 0x3bc (0x278 + 4 * k) && Nat.blt (0x278 + 4 * k) 0x3f0)) = true := by
  decide +kernel


/-- (4) Every PC fetched by a verified body path is in the step certificates' code scope. The plan steps
(path, k, entry offset, word) are exactly the fetched instructions of the step certificates, and every byte of
each fetched word is in `HeapV2StepCerts.codeScope`. The plan's kernel-decided `steps_in_codeWords` is composed
with the scope's definition. -/
theorem plan_fetch_in_codeScope : ∀ s ∈ HeapV2Plan.steps, ∀ i < 4,
    HeapV2StepCerts.codeScope (HeapV2.entryOffset + s.2.2.1 + i) := by
  intro s hs i hi
  have hc : (s.2.2.1, s.2.2.2) ∈ HeapV2Plan.codeWords := by
    simpa using List.all_eq_true.1 HeapV2Plan.steps_in_codeWords s hs
  show _ ∈ HeapV2StepCerts.codeOffsets
  simp only [HeapV2StepCerts.codeOffsets, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨_, hc, i, hi, rfl⟩

/-- Every fetched body PC (file offset) is a covered word. -/
theorem plan_fetch_covered : ∀ s ∈ HeapV2Plan.steps, 0x278 + s.2.2.1 ∈ coveredOffsets := by
  intro s hs
  have hc : (s.2.2.1, s.2.2.2) ∈ HeapV2Plan.codeWords := by
    simpa using List.all_eq_true.1 HeapV2Plan.steps_in_codeWords s hs
  simp only [coveredOffsets, coveredWords, List.map_append, List.map_map, List.mem_append, List.mem_map]
  exact Or.inl ⟨_, hc, rfl⟩

/-- Every fetched shim PC (file offset) is a covered word. -/
theorem shim_fetch_covered : ∀ s ∈ HeapV2ShimPlan.steps, 0x548 + s.2.1 ∈ coveredOffsets := by
  intro s hs
  have hc : (s.2.1, s.2.2) ∈ HeapV2ShimPlan.codeWords := by
    simpa using List.all_eq_true.1 HeapV2ShimPlan.steps_in_codeWords s hs
  simp only [coveredOffsets, coveredWords, List.map_append, List.map_map, List.mem_append, List.mem_map]
  exact Or.inr ⟨_, hc, rfl⟩

end ReleaseProfile.GB10.HeapCoverage

#print axioms ReleaseProfile.GB10.HeapCoverage.trap_bytes
#print axioms ReleaseProfile.GB10.HeapCoverage.covered_closed
#print axioms ReleaseProfile.GB10.HeapCoverage.memmove_disjoint
#print axioms ReleaseProfile.GB10.HeapCoverage.harnessBytes_24
#print axioms ReleaseProfile.GB10.HeapCoverage.coveredWords_bytes
#print axioms ReleaseProfile.GB10.HeapCoverage.rx_partition
#print axioms ReleaseProfile.GB10.HeapCoverage.plan_fetch_in_codeScope
#print axioms ReleaseProfile.GB10.HeapCoverage.plan_fetch_covered
#print axioms ReleaseProfile.GB10.HeapCoverage.shim_fetch_covered
