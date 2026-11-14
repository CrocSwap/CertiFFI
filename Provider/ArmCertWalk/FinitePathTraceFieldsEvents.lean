import ArmCertWalk.FinitePathTraceEvents
import ArmCertWalk.NoUpdatePath
import ArmCertWalk.StepDescs
import ArmCertWalk.WalkAddressFacts
import ArmCertTranslateModel.SwapEvents

import ArmCertWalk.WalkSlots
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- Execute the existing finite topology path using the ACTUAL source body.
Each descriptor is recovered from the current image after preceding stores.
The canonical inherited prior is constructed along this same source trace. -/
theorem finite_path_trace_fields_events {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (va : BitVec 64) (acc : AccessDescriptor) (startlevel : Int)
    {level bits : Nat} {base : BitVec 48} {endpoint : S1LogicalReference.PathEnd}
    (path : S1LogicalReference.Path (logicalObserve spec.logicalRows)
      (effectiveBits spec.physicalConfig).toNat va level bits base endpoint)
    (leafLevel leafLogical : Nat) (leafPhysical : FullAddress) (leafView : S1DescriptorPIE.View 64)
    (successful : endpoint = .leaf leafLevel leafLogical leafPhysical leafView)
    (leafUsed : rowsObserve spec.imageRows leafPhysical.address.toNat true leafView)
    (current : TTWState) (alignedInput : Bool) (descaddr : FullAddress) (oldDescriptor : BitVec 64)
    (typ : DescriptorType) (fault : FaultRecord) (a64 s2 : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (initial : State)
    (format : WalkFormat spec.params spec.physicalConfig spec.controls)
    (callees : WalkCalleesAt spec.params spec.physicalConfig spec.controls config initial)
    (image : TopologyImageAt spec initial)
    (attributes : AttributeImage (rowsObserve spec.imageRows) config initial.mem)
    (ss : acc.ss = .SS_NonSecure) (noFault : fault.statuscode = .Fault_None)
    (nonsecure : current.baseaddress.paspace = .PAS_NonSecure)
    (currentLevel : current.level = (level : Int)) (currentDisCH : current.disch = 0#1)
    (slot : descaddr.address.toNat = S1LogicalReference.entryAddress base va level bits)
    (space : descaddr.paspace = .PAS_NonSecure) :
    ∃ (steps : Nat) (out : WalkVars) (other : State) (words : List (BitVec 64))
      (prior : S1LogicalReference.TablePermissions) (operations : List TableUpdate),
      0 < steps ∧ (steps ≤ 4 - level ∧ steps = leafLevel + 1 - level) ∧
      S2Loop.Trace walkStop (S1WalkSource.named.body0 spec.params va .Regime_EL20 acc 64 startlevel)
        steps (alignedInput, descaddr, oldDescriptor, typ, fault, a64, s2, skl, walkaddr, current)
        initial (.ok out) other ∧
      PathPermissionAnnotation (logicalObserve spec.logicalRows) (effectiveBits spec.physicalConfig).toNat
        va spec.controls path (nativeTablePermissionProjection current.permissions) words prior ∧
      WalkLeafEndpoint spec.params config spec.controls (outputOverlayEnabled initial.regs)
        leafLevel leafPhysical leafView prior out other ∧ other.regs = initial.regs ∧
      StoreHistory spec.params (rowsFootprint spec.imageRows) initial.mem operations other.mem ∧
      (walkAddress out).paddress = leafPhysical ∧ (walkAddress out).vaddress = walkaddr.vaddress ∧
      ∃ traffic : List (Nat × Bool × Array Event), traffic.length = steps ∧
        WalkTrafficFrom initial.events traffic other.events ∧
        (RawImageAt spec.imageRows initial.mem → NoUpdateRows spec.params acc spec.imageRows = true →
          (∀ step ∈ traffic, step.2.1 = false) ∧ operations = []) ∧
        ((traffic.map (·.1)).Nodup → ∃ descs, StepDescs spec.params initial.mem traffic descs) ∧
        (∀ op ∈ operations, ∃ step ∈ traffic, step.1 = op.slot ∧ step.2.1 = true) ∧
        (∃ step ∈ traffic, step.1 = leafPhysical.address.toNat ∧ step.2.1 = false) ∧
        ((spec.logicalRows.map (·.logical)).Nodup →
          traffic.map (·.1) = walkSlots spec.logicalRows va (4 - level) level bits base) := by
  cases path with
  | invalid level bits base physical view valid aligned observed kind => cases successful
  | range level bits base physical view valid aligned observed kind outOfRange => cases successful
  | leaf level bits base physical view valid aligned observed kind =>
    have actual := observed_actual_slot spec _ physical view observed descaddr slot space
    subst physical
    injection successful with levelEq logicalEq physicalEq viewEq
    subst leafLevel
    subst leafLogical
    subst leafPhysical
    subst leafView
    obtain ⟨role, used⟩ := spec.represented _ _ _ observed
    obtain ⟨descriptor, bytes, rawView, _⟩ := image _ role view used
    have rawKind := descriptor_leaf_kind _ _ _ descriptor view rawView level valid kind
    rw [← currentLevel] at rawKind
    have encoded : S2Endian.encode spec.params.ee descriptor = descriptor := by
      simp [format.endian, S2Endian.encode]
    obtain ⟨next, readBase, other, readTTW, bodyCall, meaning, registers, memory, events⟩ :=
      outer_leaf_ttw_total config spec.controls spec.params va acc startlevel alignedInput descaddr oldDescriptor
        typ fault a64 s2 skl walkaddr current level descriptor initial
        format.d128 format.ds format.tg format.aie format.pnch nonsecure ss currentLevel rawKind
        callees.attributes (attributes _ _ leafUsed descriptor bytes) callees.permissions noFault
        callees.el callees.noRME callees.aarch64 callees.el3A64 callees.noEL3A32
        (spec.available _ _ _ observed).2.2 (by simpa only [encoded] using bytes)
    let out : WalkVars := (alignedInput, descaddr, descriptor, .DescriptorType_Leaf,
      {fault with level := current.level}, a64, s2, skl, {walkaddr with paddress := descaddr}, next)
    refine ⟨1, out, other, [], nativeTablePermissionProjection current.permissions, [],
      by decide, ⟨by omega, by omega⟩, .done bodyCall (by rfl), ?_, ?_, registers, ?_, rfl, rfl,
      [(descaddr.address.toNat, false, #[descriptorReadEvent
        (S1ReadAccDesc.value (current.level == startlevel) (AArch64_GetVARange va) acc readBase)
        {walkaddr with paddress := descaddr}
        (S1OuterSplit.info spec.params .Regime_EL20 current {walkaddr with paddress := descaddr})])],
      rfl, ⟨?_, ?_⟩, fun _ _ => ⟨fun step member => by
        simp only [List.mem_singleton] at member; rw [member], rfl⟩,
      fun _ => ⟨[descriptor], .last (spec.available _ _ _ observed).2.1 (by simpa only [encoded] using bytes)⟩,
      fun op member => by simp at member,
      ⟨_, List.mem_singleton_self _, rfl, rfl⟩, ?_⟩
    · exact .leaf level bits base descaddr view valid aligned observed kind _
    · refine ⟨current, descriptor, currentLevel, currentDisCH, rfl, rawView, ?_, rfl, rfl, rfl, noFault, meaning⟩
      simpa only [memory] using bytes
    · simpa only [memory] using (StoreHistory.nil initial.mem :
        StoreHistory spec.params (rowsFootprint spec.imageRows) initial.mem [] initial.mem)
    · simp only [List.foldl_cons, List.foldl_nil]
      rw [events, Array.push_eq_append]
    · intro step member
      simp only [List.mem_singleton] at member
      subst member
      exact ⟨_, _, _, readTTW, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · intro nodup
      have fuel : 4 - level = (3 - level) + 1 := by omega
      rw [fuel, walk_slots_leaf spec.logicalRows nodup va (3 - level) level bits base descaddr view observed kind]
      simp [slot]
  | table level bits base physical view endpoint valid aligned observed kind inRange tail =>
    have actual := observed_actual_slot spec _ physical view observed descaddr slot space
    subst physical
    obtain ⟨role, used⟩ := spec.represented _ _ _ observed
    obtain ⟨descriptor, bytes, rawView, _⟩ := image _ role view used
    have rawKind := descriptor_table_kind _ _ _ descriptor view rawView level (by omega) kind
    rw [← currentLevel] at rawKind
    have child := descriptor_child_base _ _ _ descriptor view rawView
    have bound : S1LogicalReference.entryAddress ((S1LogicalReference.pageBase descriptor).setWidth 48)
        va (level + 1) 9 < 2 ^ (effectiveBits spec.physicalConfig).toNat := by
      rw [← child]; exact inRange
    have encoded : S2Endian.encode spec.params.ee descriptor = descriptor := by
      simp [format.endian, S2Endian.encode]
    have available := spec.available _ _ _ observed
    obtain ⟨next, address, readBase, middle, readTTW, bodyCall, nextMeaning, nextBase, nextPermissions,
      nextSpace, nextSlot, registers, history, events⟩ :=
      outer_table_ttw_total spec.params spec.physicalConfig spec.controls (rowsFootprint spec.imageRows)
        va acc startlevel alignedInput descaddr oldDescriptor typ fault a64 s2 skl walkaddr current level descriptor initial
        format.d128 format.ds format.tg format.ips callees.physical nonsecure currentLevel valid
        callees.permissions.regime format.hpd callees.permissions.pie bound rawKind noFault
        callees.el callees.noRME callees.aarch64 callees.el3A64 callees.noEL3A32
        available.2.2 (rows_covered spec.imageRows _ role view used) available.2.1
        (by simpa only [encoded] using bytes)
    have nextImage : TopologyImageAt spec middle :=
      history.preserves_image format.endian spec.aligned image
    have nextAttributes : AttributeImage (rowsObserve spec.imageRows) config middle.mem :=
      history.preserves_attributes format.endian spec.aligned attributes
    have nextLevel : next.level = ((level + 1 : Nat) : Int) := by
      have increment := nextMeaning.2.1
      omega
    have nextDisCH : next.disch = 0#1 := nextMeaning.2.2.2.2.2.2.1
    have sourceSlot : address.address.toNat =
        S1LogicalReference.entryAddress (S1LogicalReference.childBase view) va (level + 1) 9 := by
      rw [child]; exact nextSlot
    obtain ⟨steps, out, other, words, prior, operations, positive, stepBound, trace,
      annotation, meaning, tailRegs, tailHistory, leafAddress, inputVA, tailTraffic, tailLength, ⟨tailEvents, tailSteps⟩, tailCond, tailDescs, tailOps, tailLeaf, tailSlots⟩ :=
      finite_path_trace_fields_events spec config va acc startlevel tail leafLevel leafLogical leafPhysical leafView
        successful leafUsed next alignedInput address (S1TableUpdate.word spec.params descriptor)
        .DescriptorType_Table {fault with level := current.level} a64 s2 0#2 {walkaddr with paddress := descaddr}
        middle format (callees.of_regs registers) nextImage nextAttributes ss noFault
        nextMeaning.2.2.2.1 nextLevel nextDisCH sourceSlot nextSpace
    have nextPrior : nativeTablePermissionProjection next.permissions =
        S1LogicalReference.tablePermissions spec.controls
          (nativeTablePermissionProjection current.permissions) view.stable :=
      nextPermissions.trans (table_permissions_view _ _ _ _ _ descriptor view rawView)
    rw [nextPrior] at annotation
    have headStep : ∃ (updated : Bool) (delta : Array Event),
        WalkStepTraffic descaddr.address.toNat updated delta ∧ middle.events = initial.events ++ delta ∧
        (S1TableUpdate.word spec.params descriptor = descriptor → updated = false) ∧
        (¬ S1TableUpdate.word spec.params descriptor = descriptor → updated = true) := by
      by_cases same : S1TableUpdate.word spec.params descriptor = descriptor
      · simp only [same, ↓reduceIte] at events
        exact ⟨false, _, ⟨_, _, _, readTTW, rfl, Or.inl ⟨rfl, rfl⟩⟩, by rw [events, Array.push_eq_append]; try rfl,
          fun _ => rfl, fun h => absurd same h⟩
      · simp only [same, ↓reduceIte] at events
        obtain ⟨updateBase, updateTTW, updated⟩ := events
        let readAcc := S1ReadAccDesc.value (current.level == startlevel) (AArch64_GetVARange va) acc readBase
        let addr : AddressDescriptor := {walkaddr with paddress := descaddr}
        let ti := S1OuterSplit.info spec.params .Regime_EL20 current addr
        let updAcc := S1AccDescFrame.updated acc updateBase
        refine ⟨true, #[descriptorReadEvent readAcc addr ti, swapReadEvent updAcc addr,
          swapWriteEvent spec.params.ee (S1TableUpdate.word spec.params descriptor) updAcc addr],
          ⟨readAcc, addr, ti, readTTW, rfl, Or.inr ⟨rfl, updAcc, spec.params.ee,
            S1TableUpdate.word spec.params descriptor, updateTTW, rfl⟩⟩, ?_, fun h => absurd h same, fun _ => rfl⟩
        rw [updated]
        simp only [Array.push_eq_append, Array.append_assoc]
        rfl
    obtain ⟨updated, delta, stepTraffic, middleEvents, noFlag, yesFlag⟩ := headStep
    obtain ⟨tailLe, tailEq⟩ := stepBound
    refine ⟨steps + 1, out, other, view.stable :: words, prior,
      tableOperations spec.params descaddr.address.toNat descriptor ++ operations,
      by omega, ⟨by omega, by omega⟩, .next bodyCall (by rfl) trace, ?_, ?_, tailRegs.trans registers,
      history.append tailHistory, leafAddress, inputVA, (descaddr.address.toNat, updated, delta) :: tailTraffic,
      by simp only [List.length_cons, tailLength], ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · exact .table level bits base descaddr view endpoint valid aligned observed kind inRange tail
        (nativeTablePermissionProjection current.permissions) prior words annotation
    · simpa only [registers] using meaning
    · simp only [List.foldl_cons]
      rw [← middleEvents]
      exact tailEvents
    · intro step member
      simp only [List.mem_cons] at member
      rcases member with rfl | inTail
      · exact stepTraffic
      · exact tailSteps step inTail
    · intro rawImg none
      obtain ⟨row, member, slotEq, _, _⟩ := used
      have present : S1ByteMemory.DescAt initial.mem row.slot descriptor := by
        rw [← slotEq]; simpa only [encoded] using bytes
      have isRaw := raw_at_slot rawImg member present
      have same : S1TableUpdate.word spec.params descriptor = descriptor := by
        rw [isRaw]; exact table_no_update none member
      have noOps : tableOperations spec.params descaddr.address.toNat descriptor = [] := by
        simp [tableOperations, same]
      rw [noOps] at history
      have middleMem : middle.mem = initial.mem := history_nil_mem history
      have rawMiddle : RawImageAt spec.imageRows middle.mem := by rw [middleMem]; exact rawImg
      obtain ⟨tailFlags, tailOps⟩ := tailCond rawMiddle none
      refine ⟨?_, by rw [noOps, tailOps]; rfl⟩
      intro step member
      simp only [List.mem_cons] at member
      rcases member with rfl | inTail
      · exact noFlag same
      · exact tailFlags step inTail
    · intro nodup
      simp only [List.map_cons, List.nodup_cons] at nodup
      obtain ⟨headFresh, tailNodup⟩ := nodup
      obtain ⟨descs, tailRel⟩ := tailDescs tailNodup
      have slotAligned : descaddr.address.toNat % 8 = 0 := available.2.1
      have presentHead : S1ByteMemory.DescAt initial.mem descaddr.address.toNat descriptor := by
        simpa only [encoded] using bytes
      have flagEq : updated = !decide (S1TableUpdate.word spec.params descriptor = descriptor) := by
        by_cases same : S1TableUpdate.word spec.params descriptor = descriptor
        · simp [noFlag same, same]
        · simp [yesFlag same, same]
      have tailInitial := tailRel.transport (m := initial.mem) (fun step member d present => by
        have aligned := tailRel.slots_aligned step member
        have notHead : step.1 ≠ descaddr.address.toNat := by
          intro equal; apply headFresh; rw [← equal]; exact List.mem_map_of_mem member
        refine (desc_at_history_outside history step.1 d aligned ?_).mp present
        intro op opMember
        unfold tableOperations at opMember
        split at opMember
        · simp at opMember
        · simp only [List.mem_singleton] at opMember
          rw [opMember]; exact fun h => notHead h.symm)
      exact ⟨descriptor :: descs, .table slotAligned presentHead flagEq tailInitial⟩
    · intro op member
      rcases List.mem_append.mp member with headOp | tailOp
      · unfold tableOperations at headOp
        split at headOp
        · simp at headOp
        · rename_i different
          simp only [List.mem_singleton] at headOp
          subst headOp
          exact ⟨_, List.mem_cons_self, rfl, yesFlag different⟩
      · obtain ⟨step, stepMember, slotEq, flag⟩ := tailOps op tailOp
        exact ⟨step, List.mem_cons_of_mem _ stepMember, slotEq, flag⟩
    · obtain ⟨step, stepMember, slotEq, flag⟩ := tailLeaf
      exact ⟨step, List.mem_cons_of_mem _ stepMember, slotEq, flag⟩
    · intro nodup
      have fuel : 4 - level = (4 - (level + 1)) + 1 := by omega
      rw [fuel, walk_slots_table spec.logicalRows nodup va (4 - (level + 1)) level bits base descaddr view observed kind,
        List.map_cons, tailSlots nodup, slot]
termination_by 4 - level
decreasing_by omega

#print axioms finite_path_trace_fields_events
end ArmCertWalk
