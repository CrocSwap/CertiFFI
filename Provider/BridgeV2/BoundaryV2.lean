import Bridge.Boundary
import BridgeV2.StateProjectionM
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.Boundary ArmCert.Premises.TranslationAgreesV1
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to BridgeV2.BoundaryV2LNSym.
namespace ArmBridge.BoundaryV2

/- Boundary v2. The v1 boundary (SEAL f1f701c8:
   formStep, SysregMove, Premises, FetchOK) is reused unchanged; v2 adds the map-keyed
   projection and the translation premises. The ConsumerMap m is ONE parameter for the
   whole run (no remap): every per-step premise below is stated for the same m. -/

/-- The EL0 NonSecure instruction-fetch access shape (v2:, = MemM1 AccIF; the
    actual CreateAccDescIFetch at EL0 returns such a descriptor). -/
structure IFetchAcc0 (acc : AccessDescriptor) : Prop where
  ifetch : acc.acctype = .AccessType_IFETCH
  el : acc.el = 0#2
  ss : acc.ss = .SS_NonSecure
  ls64 : acc.ls64 = false
  tx : acc.transactional = false
  nf : acc.nonfault = false
  ff : acc.firstfault = false

/-- VA bytes covered by some permitted access of m (byte footprint). -/
def PermVA (m : ConsumerMap) (a : BitVec 64) : Prop :=
  ∃ (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (size : Int) (i : Nat),
    m.permitted va acc aligned size ∧ (i : Int) < size ∧
    a = va + BitVec.ofNat 64 i

/-- Physical bytes the consumer can see through m (images of permitted VA bytes). -/
def MappedPA (m : ConsumerMap) (p : Nat) : Prop :=
  ∃ a, PermVA m a ∧ (m.pa a).toNat = p

/-- Unprojected RAM is untouched from s to s': every native byte that is neither consumer-mapped
    nor a table byte is unchanged (defects 06fe condition 3). -/
def UnmappedSame (m : ConsumerMap) (s s' : NativeState) : Prop :=
  ∀ p, ¬ MappedPA m p → ¬ m.tableByte p → s'.mem.get? p = s.mem.get? p

theorem UnmappedSame.refl (m : ConsumerMap) (s : NativeState) : UnmappedSame m s s :=
  fun _ _ _ => rfl

theorem UnmappedSame.trans {m : ConsumerMap} {s t u : NativeState}
    (h1 : UnmappedSame m s t) (h2 : UnmappedSame m t u) : UnmappedSame m s u :=
  fun p hp ht => (h2 p hp ht).trans (h1 p hp ht)

/-- Map-level side conditions (all on m alone, fixed over the run). -/
structure MapOK (m : ConsumerMap) : Prop where
  /-- A permitted access of `size` bytes at va touches PA bytes m.pa va, +1, ...: the map is
      PA-contiguous over each permitted access (true for page maps and non-crossing accesses). -/
  contiguous : ∀ (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (size : Int) (i : Nat),
    m.permitted va acc aligned size → (i : Int) < size →
    (m.pa (va + BitVec.ofNat 64 i)).toNat = (m.pa va).toNat + i
  /-- Table bytes are disjoint from every permitted byte (translation-side AF/DBM writes never
      land on consumer-visible bytes). -/
  tableDisjoint : ∀ a, PermVA m a → ¬ m.tableByte (m.pa a).toNat
  /-- m.pa is injective on permitted bytes, so LNSym write sets map one-to-one to PA. -/
  injective : ∀ a b, PermVA m a → PermVA m b → m.pa a = m.pa b → a = b
  /-- v7 (, crypto e2c6): no VA at all (permitted or not) aliases a permitted byte's PA,
      so projectM agrees with the native byte at every VA after a store to a permitted VA.
      Shared mappings are out of scope. -/
  injectiveFromPermitted : ∀ a b, PermVA m a → m.pa b = m.pa a → b = a

end ArmBridge.BoundaryV2

