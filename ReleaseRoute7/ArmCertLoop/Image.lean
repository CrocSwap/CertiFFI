import ArmCertPipe.FetchG
import ArmCertLoop.SpanMap

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

namespace ArmCertLoop.Image

/-- A finite static instruction image. Length describes code size, never loop
trip count. Binding the exact sealed ELF bytes remains a separate RunCheck. -/
def wordImage (start : Nat) (words : List (BitVec 32)) : MemReloc.Image :=
  fun off => if start ≤ off ∧ off < start + 4 * words.length then
    some ((words.getD ((off - start) / 4) 0).extractLsb' (8 * ((off - start) % 4)) 8)
  else none

theorem image_word (start : Nat) (words : List (BitVec 32)) (i : Nat) (room : i < words.length)
    (k : Nat) (byte : k < 4) :
    wordImage start words (start + 4 * i + k) =
      some ((words.getD i 0).extractLsb' (8 * k) 8) := by
  have inside : start ≤ start + 4 * i + k ∧ start + 4 * i + k < start + 4 * words.length := by omega
  have diff : start + 4 * i + k - start = 4 * i + k := by omega
  have quotient : (4 * i + k) / 4 = i := by omega
  have remainder : (4 * i + k) % 4 = k := by omega
  simp only [wordImage, ite_eq_left inside, diff, quotient, remainder]

def codeVAs (base : BitVec 64) (start : Nat) (words : List (BitVec 32)) : List (BitVec 64) :=
  (List.range words.length).map fun i => MemReloc.imageAddress base (start + 4 * i)

theorem codeVA_member (base : BitVec 64) (start : Nat) (words : List (BitVec 32))
    (i : Nat) (room : i < words.length) :
    MemReloc.imageAddress base (start + 4 * i) ∈ codeVAs base start words := by
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr room, rfl⟩

/-- Use the existing actual-fetch pipeline with a symbolic data-span consumer
and one statically indexed code word. The loop's native invariant supplies the
reached PC; the image word is proved here, not a future-call hypothesis. -/
def fetch_word {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (spans : List SpanMap.Span) (table scope : Nat → Prop)
    (base : BitVec 64) (start : Nat) (words : List (BitVec 32))
    (offset : Nat → BitVec 64) (budget elapsed : Nat) (i : Nat) (room : i < words.length)
    (x : NativeState)
    (inv : ChainInv2 spec config rows mapping
      (SpanMap.consumerMap spans (codeVAs base start words) mapping table)
      scope (wordImage start words) base base offset budget elapsed x)
    (pc : x.regs._PC = MemReloc.imageAddress base (start + 4 * i))
    (inside : ∀ k, k < 4 → scope (start + 4 * i + k))
    (contiguous : ImageWordContiguous mapping base (start + 4 * i))
    (mmio : MappedNotMMIO mapping (MemReloc.imageAddress base (start + 4 * i)))
    (separated : ImageTableSeparated scope base mapping (rowsFootprint spec.imageRows).byte) :
    FetchObligations spec config rows mapping (words.getD i 0) x :=
  ArmCertPipe.fetchG spec config rows mapping _ scope (wordImage start words) base base offset budget elapsed x
    inv (start + 4 * i) (words.getD i 0) pc inside contiguous mmio separated
    (image_word start words i room)
    (fun acc shape => by
      rw [pc]
      exact SpanMap.fetch_permitted spans (codeVAs base start words) mapping table _
        (codeVA_member base start words i room) acc shape)

#print axioms image_word
#print axioms codeVA_member
#print axioms fetch_word

end ArmCertLoop.Image
