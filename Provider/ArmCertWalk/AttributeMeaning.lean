import ArmCertWalk.MAIRActive
import Walk.S1LogicalReferenceTypes

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

open S1LogicalReference (CacheView AttributeKind)

/-- NC hints are inactive. A transient bit is also inactive with no allocation
hint: the canonical decoder leaves it undefined in that case. -/
def cacheProjection (cache : MemAttrHints) : CacheView :=
  { attrs := cache.attrs
    hints := if cache.attrs = MemAttr_NC then none else some cache.hints
    transient := if cache.attrs = MemAttr_NC ∨ cache.hints = MemHint_No then none
      else some cache.transient }

def cachePolicy (nibble : BitVec 4) : BitVec 2 :=
  if nibble.getLsbD 2 then
    if nibble = 4#4 then MemAttr_NC else MemAttr_WB
  else MemAttr_WT

def cacheHints (nibble : BitVec 4) : BitVec 2 :=
  if nibble.extractLsb' 0 2 = 0#2 then MemHint_No
  else if nibble.extractLsb' 0 2 = 1#2 then MemHint_WA
  else if nibble.extractLsb' 0 2 = 2#2 then MemHint_RA
  else MemHint_RWA

def decodedCache (nibble : BitVec 4) : CacheView :=
  { attrs := cachePolicy nibble
    hints := if cachePolicy nibble = MemAttr_NC then none else some (cacheHints nibble)
    transient := if cachePolicy nibble = MemAttr_NC ∨ cacheHints nibble = MemHint_No then none
      else some (!nibble.getLsbD 3) }

def deviceKind (bits : BitVec 2) : DeviceType :=
  if bits = 0#2 then .DeviceType_nGnRnE
  else if bits = 1#2 then .DeviceType_nGnRE
  else if bits = 2#2 then .DeviceType_nGRE
  else .DeviceType_GRE

/-- The deterministic active body is separate from source shareability choice. -/
structure AttributeBody where
  kind : AttributeKind
  tags : MemTagType
  noTagAccess : Bool
  xs : BitVec 1
  deriving BEq, Repr

def attributeProjection (attrs : MemoryAttributes) : AttributeBody :=
  { kind := match attrs.memtype with
      | .MemType_Device => .device attrs.device
      | .MemType_Normal => .normal (cacheProjection attrs.inner) (cacheProjection attrs.outer)
    tags := attrs.tags
    noTagAccess := attrs.notagaccess
    xs := attrs.xs }

def decodedAttributeBody (attr : BitVec 8) (mtx : BitVec 1) : AttributeBody :=
  let nc : CacheView := ⟨MemAttr_NC, none, none⟩
  let wt : CacheView := ⟨MemAttr_WT, some MemHint_RA, some false⟩
  let wb : CacheView := ⟨MemAttr_WB, some MemHint_RWA, some false⟩
  let inner := decodedCache (attr.extractLsb' 0 4)
  let outer := decodedCache (attr.extractLsb' 4 4)
  { kind := if attributeHigh attr = 0#4 then .device (deviceKind (attr.extractLsb' 2 2))
      else if attr = 64#8 then .normal nc nc
      else if attr = 160#8 then .normal wt wt
      else if attr = 240#8 then .normal wb wb
      else .normal inner outer
    tags := if attr = 240#8 then .MemTag_AllocationTagged
      else if mtx = 1#1 then .MemTag_CanonicallyTagged else .MemTag_Untagged
    noTagAccess := false
    xs := if attributeHigh attr = 0#4 then ~~~(attr.extractLsb' 0 1)
      else if attr = 64#8 ∨ attr = 160#8 ∨ attr = 240#8 then 0#1
      else if inner.attrs = MemAttr_WB ∧ outer.attrs = MemAttr_WB then 0#1 else 1#1 }

/-- Raw SH=1 uses source ConstrainUnpredictable/undefined shareability. Retain
that nondeterminism instead of silently excluding it or choosing NSH. -/
def ShareabilityAllowed (sh : BitVec 2) (actual : Shareability) : Prop :=
  if sh = 2#2 then actual = .Shareability_OSH
  else if sh = 3#2 then actual = .Shareability_ISH
  else if sh = 0#2 then actual = .Shareability_NSH
  else True

def AttributeInterprets (attr : BitVec 8) (sh : BitVec 2) (params : S1TTWParams)
    (actual : MemoryAttributes) : Prop :=
  attributeProjection actual = decodedAttributeBody attr params.mtx ∧
    ShareabilityAllowed sh actual.shareability

end ArmCertWalk
