import NativeBodyDeploy.Assemble
import HeapV2StepCerts.Carry

set_option autoImplicit false
set_option maxHeartbeats 200000

/-!
# Discharging the closed `CodeStatic.inside` piece (gate v3 R-STATIC,)

`HeapV2StepCerts.CodeStatic.inside` is a closed proposition (`∀ code ∈ HeapV2Plan.codeWords, ∀ i < 4, codeScope …`)
proved once by the provider theorem `HeapV2StepCerts.codeScope_inside`. Retained card atoms of type `CodeStatic` /
`NativeBodyDeploy.BodyStatic` become their `…R` counterparts (every field except `inside`), and the card receives the full
structure via `toFull`, with `inside := codeScope_inside`. No other field changes.
-/

namespace ReleaseProfile.GB10

open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft HeapV2StepCerts.E17General

/-- `HeapV2StepCerts.CodeStatic` without the closed `inside` field. -/
structure CodeStaticR (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (table : Nat → Prop) : Prop where
  separated : ImageTableSeparated HeapV2StepCerts.codeScope base mapping table
  contiguous : ∀ code ∈ HeapV2Plan.codeWords, ImageWordContiguous mapping base (HeapV2.entryOffset + code.1)
  notMMIO : ∀ code ∈ HeapV2Plan.codeWords,
    MappedNotMMIO mapping (MemReloc.imageAddress base (HeapV2.entryOffset + code.1))

#check "CURRENT_DECL GB10.CodeStaticR.toFull"
theorem CodeStaticR.toFull {mapping : BitVec 64 → Option Nat} {base : BitVec 64} {table : Nat → Prop}
    (r : CodeStaticR mapping base table) : HeapV2StepCerts.CodeStatic mapping base table :=
  ⟨r.separated, HeapV2StepCerts.codeScope_inside, r.contiguous, r.notMMIO⟩

/-- `NativeBodyDeploy.BodyStatic` with `static` replaced by `CodeStaticR`. -/
structure BodyStaticR {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) : Prop where
  static : CodeStaticR mapping base (rowsFootprint spec.imageRows).byte
  dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows)
  pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0
  codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping)
  sep : RtSaved.SlotSep pins mapping
  mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n
  page : base.toNat % 4096 = 0
  low : base.toNat < 2 ^ 54
  agrees : ConsumerMapAgrees spec mapping (cmap spec mapping base pins)
  nodup : (spec.logicalRows.map (·.logical)).Nodup

#check "CURRENT_DECL GB10.BodyStaticR.toFull"
theorem BodyStaticR.toFull {domain : QueryDomain} {spec : TopologyImageSpec domain} {mapping : BitVec 64 → Option Nat}
    {base : BitVec 64} {pins : HeapV2E17.Pins} (r : BodyStaticR spec mapping base pins) :
    NativeBodyDeploy.BodyStatic spec mapping base pins :=
  ⟨r.static.toFull, r.dataStatic, r.pinAligned, r.codeD, r.sep, r.mapped, r.page, r.low, r.agrees, r.nodup⟩

/-- Any full structure gives its `…R` part (so C2 producers of the full atom still serve). -/
theorem CodeStaticR.ofFull {mapping : BitVec 64 → Option Nat} {base : BitVec 64} {table : Nat → Prop}
    (h : HeapV2StepCerts.CodeStatic mapping base table) : CodeStaticR mapping base table :=
  ⟨h.separated, h.contiguous, h.notMMIO⟩

theorem BodyStaticR.ofFull {domain : QueryDomain} {spec : TopologyImageSpec domain} {mapping : BitVec 64 → Option Nat}
    {base : BitVec 64} {pins : HeapV2E17.Pins} (h : NativeBodyDeploy.BodyStatic spec mapping base pins) :
    BodyStaticR spec mapping base pins :=
  ⟨CodeStaticR.ofFull h.static, h.dataStatic, h.pinAligned, h.codeD, h.sep, h.mapped, h.page, h.low, h.agrees, h.nodup⟩

end ReleaseProfile.GB10

#print axioms ReleaseProfile.GB10.CodeStaticR.toFull
#print axioms ReleaseProfile.GB10.BodyStaticR.toFull
