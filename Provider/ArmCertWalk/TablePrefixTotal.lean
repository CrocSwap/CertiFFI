import ArmCertWalk.NextTableTotal
import ArmCertWalk.NextEntryTotal

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

structure TablePrefixCertificate (params : S1TTWParams) (config : PhysicalConfig)
    (controls : S1LogicalReference.Controls) (current : TTWState) (level : Nat)
    (descriptor va : BitVec 64) (s2 : Bool) (initial : State) where
  next : TTWState
  address : FullAddress
  afterNext : State
  afterEntry : State
  state : State
  nextCall : AArch64_S1NextWalkStateTable current s2 .Regime_EL20 params descriptor initial = .ok next afterNext
  entryCall : AArch64_TTEntryAddress next.level params.d128 0#2 params.tgx params.txsz va next.baseaddress afterNext =
    .ok address afterEntry
  rangeCall : AArch64_OAOutOfRange address.address params.d128 params.ps params.tgx afterEntry = .ok false state
  nextMeaning : NextTableMeaning params current descriptor next
  nextBase : next.baseaddress.address = S1LogicalReference.pageBase descriptor
  nextPermissions : nativeTablePermissionProjection next.permissions =
    S1LogicalReference.tablePermissions controls (nativeTablePermissionProjection current.permissions) descriptor
  addressSpace : address.paspace = .PAS_NonSecure
  addressSlot : address.address.toNat = S1LogicalReference.entryAddress
    ((S1LogicalReference.pageBase descriptor).setWidth 48) va (level + 1) 9
  registers : state.regs = initial.regs
  memory : state.mem = initial.mem
  events : state.events = initial.events

/-- This certificate is constructed internally from actual source callees;
no successful source call is required as a public entry hypothesis. -/
theorem table_prefix_total (params : S1TTWParams) (config : PhysicalConfig)
    (controls : S1LogicalReference.Controls) (current : TTWState) (level : Nat)
    (descriptor va : BitVec 64) (s2 : Bool) (initial : State)
    (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) (tg : params.tgx = .TGx_4KB)
    (ips : params.ps = config.ips) (physical : PhysicalAt config initial)
    (nonsecure : current.baseaddress.paspace = .PAS_NonSecure)
    (currentLevel : current.level = (level : Int)) (valid : level < 3)
    (regime : controls.regime = .el20)
    (hpd : controls.hpd = (params.hpd == 1#1)) (pie : controls.pie = (params.pie == 1#1))
    (bound : S1LogicalReference.entryAddress ((S1LogicalReference.pageBase descriptor).setWidth 48)
      va (level + 1) 9 < 2 ^ (effectiveBits config).toNat) :
    Nonempty (TablePrefixCertificate params config controls current level descriptor va s2 initial) := by
  obtain ⟨next, afterNext, nextCall, nextMeaning, nextBase, nextPermissions, nextRegs, nextMem, nextEvents⟩ :=
    next_table_canonical_total params current descriptor s2 initial controls d128 ds tg nonsecure regime hpd pie
  have nextLevel : next.level = ((level + 1 : Nat) : Int) := by
    have increment := nextMeaning.2.1
    omega
  have aligned : next.baseaddress.address.toNat % 4096 = 0 := by
    rw [nextBase]
    have shape := S1EntryNextGeometry.base_shape descriptor
    have baseEq : S1NextTable10Facts.base descriptor = S1LogicalReference.pageBase descriptor :=
      source_table_base_eq descriptor
    simpa only [baseEq] using shape.1
  have width : next.baseaddress.address.toNat < 2^48 := by
    rw [nextBase]
    have shape := S1EntryNextGeometry.base_shape descriptor
    have baseEq : S1NextTable10Facts.base descriptor = S1LogicalReference.pageBase descriptor :=
      source_table_base_eq descriptor
    simpa only [baseEq] using shape.2
  obtain ⟨address, afterEntry, state, entryCall, rangeCall, space, slot, registers, memory, events⟩ :=
    next_entry_range_total params config (level + 1) va next.baseaddress afterNext (by omega) aligned width
      (physical.of_regs nextRegs) d128 tg ips (by simpa only [nextBase] using bound)
  refine ⟨{
    next := next
    address := address
    afterNext := afterNext
    afterEntry := afterEntry
    state := state
    nextCall := nextCall
    entryCall := ?_
    rangeCall := rangeCall
    nextMeaning := nextMeaning
    nextBase := nextBase
    nextPermissions := nextPermissions
    addressSpace := space.trans nextMeaning.2.2.2.1
    addressSlot := ?_
    registers := registers.trans nextRegs
    memory := memory.trans nextMem
    events := events.trans nextEvents
  }⟩
  · simpa only [nextLevel] using entryCall
  · simpa only [nextBase] using slot

#print axioms table_prefix_total
end ArmCertWalk
