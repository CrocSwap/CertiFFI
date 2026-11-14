import ArmFull
open Sail ArmFull
namespace S1LogicalReference

/- Shared semantic data only. No source transition, source replay, oracle
   execution, or callee-success premise defines these outcomes. -/
inductive Regime where
  | el10 | el20
  deriving DecidableEq, BEq, Repr, Inhabited
inductive Privilege where
  | unprivileged | privileged
  deriving DecidableEq, BEq, Repr, Inhabited
inductive Access where
  | read | write | execute
  deriving DecidableEq, BEq, Repr, Inhabited
inductive AccessClass where
  | data | tableWalk | instruction | addressTranslate | cacheInstruction | cacheData
  deriving DecidableEq, BEq, Repr, Inhabited
structure Rights where
  read : Bool
  write : Bool
  execute : Bool
  deriving DecidableEq, BEq, Repr, Inhabited
/- Retain the complete input access descriptor as data: read/write are
   independent, and cache operation/scope, PAN, RCW and other distinctions
   must not be collapsed to a single read/write/execute label. -/
structure Request where
  raw : AccessDescriptor
  aligned : Bool
  deriving BEq, Repr, Inhabited

/- Only fields defined by S1 table/leaf interpretation are compared. The
   unrelated S2 fields and inactive classic/PIE fields of Sail.Permissions
   remain unconstrained at the source bridge. -/
structure TablePermissions where
  ap : BitVec 2
  pxn : Bool
  uxn : Bool
  deriving DecidableEq, BEq, Repr, Inhabited
structure ClassicPermissions where
  ap : BitVec 2
  pxn : Bool
  uxn : Option Bool
  deriving DecidableEq, BEq, Repr, Inhabited
structure IndirectPermissions where
  privileged : BitVec 4
  unprivileged : BitVec 4
  notDirty : Bool
  deriving DecidableEq, BEq, Repr, Inhabited
inductive LeafPermissions where
  | classic (value : ClassicPermissions)
  | indirect (value : IndirectPermissions)
  deriving DecidableEq, BEq, Repr, Inhabited
structure Permissions where
  table : TablePermissions
  leaf : LeafPermissions
  overlayIndex : Option (BitVec 4)
  deriving DecidableEq, BEq, Repr, Inhabited

/- Inactive fields of the source attribute record are not semantic data. In
   particular Device cache fields, Normal device type, and NC hints can be
   undefined for different source oracles. -/
structure CacheView where
  attrs : BitVec 2
  hints : Option (BitVec 2)
  transient : Option Bool
  deriving DecidableEq, BEq, Repr, Inhabited
inductive AttributeKind where
  | device (kind : DeviceType)
  | normal (inner outer : CacheView)
  deriving BEq, Repr, Inhabited
structure AttributeView where
  kind : AttributeKind
  shareability : Shareability
  tags : MemTagType
  noTagAccess : Bool
  xs : BitVec 1
  deriving BEq, Repr, Inhabited

structure AttributeSelection where
  index : BitVec 4
  mairByte : BitVec 8
  decoded : AttributeView
  deriving BEq, Repr, Inhabited
structure FaultInfo where
  code : Fault
  level : Int
  secondStage : Bool
  deriving BEq, Repr, Inhabited
inductive UpdateCause where
  | tableAccessFlag | leafAccessFlag | leafDirty | leafAccessFlagAndDirty
  deriving DecidableEq, BEq, Repr, Inhabited
structure DescriptorWrite where
  slot : FullAddress
  before : BitVec 64
  after : BitVec 64
  cause : UpdateCause
  deriving BEq, Repr, Inhabited
abbrev WriteTrace := List DescriptorWrite

structure WalkLeaf where
  slot : FullAddress
  descriptor : BitVec 64
  level : Int
  base : FullAddress
  output : FullAddress
  attrs : AttributeSelection
  permissions : Permissions
  contiguous : Bool
  inheritedDisCH : Bool
  nonGlobal : Bool
  guarded : Bool
  s1Assured : Bool
  deriving BEq, Repr, Inhabited
inductive WalkOutcome where
  | fault (info : FaultInfo) (writes : WriteTrace)
  | leaf (info : WalkLeaf) (writes : WriteTrace)
  deriving BEq, Repr, Inhabited
structure Mapping where
  leaf : WalkLeaf
  rights : Rights
  outputAttrs : AttributeView
  deriving BEq, Repr, Inhabited
inductive AccessOutcome where
  | fault (info : FaultInfo) (writes : WriteTrace)
  | permitted (mapping : Mapping) (writes : WriteTrace)
  deriving BEq, Repr, Inhabited

/- Missing logical evidence is never an architectural translation fault. -/
inductive ObservationError where
  | missingDescriptor (slot : FullAddress)
  | malformedPath (level : Int)
  | unsupportedFormat
  | reservedAttribute (value : BitVec 8)
  deriving BEq, Repr, Inhabited
abbrev Evaluation (α : Type) := Except ObservationError α

structure Controls where
  regime : Regime
  paBits : Nat
  ha : Bool
  hd : Bool
  haft : Bool
  pie : Bool
  hpd : Bool
  nv1 : Bool
  el2Enabled : Bool
  pnch : Bool
  aie : Bool
  mtx : Bool
  featXS : Bool
  mte2 : Bool
  mair : BitVec 64
  mair2 : BitVec 64
  pir : BitVec 64
  pire0 : BitVec 64
  poe : Bool
  e0poe : Bool
  por : BitVec 64
  porE0 : BitVec 64
  cmow : Bool
  wxn : Bool
  uwxn : Bool
  pan : Bool
  epan : Bool
  deriving DecidableEq, BEq, Repr, Inhabited

end S1LogicalReference
