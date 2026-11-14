import ArmCertWalk.FinitePathTrace
import ArmCertWalk.OuterTableTTW
import ArmCertWalk.OuterLeafTTW
import ArmCertTranslateModel.SwapEvents
import ArmCertWalk.WalkSlots

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- The ACTUAL events of one walk step at descriptor slot `pa`: the descriptor
read, followed (table steps whose AF word changes) by the actual swap read and
swap write. Access-descriptor/TSI arguments are the actual ones (existential). -/
def WalkStepTraffic (pa : Nat) (updated : Bool) (delta : Array Event) : Prop :=
  ∃ (readAcc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo),
    readAcc.acctype = .AccessType_TTW ∧ addr.paddress.address.toNat = pa ∧
    ((updated = false ∧ delta = #[descriptorReadEvent readAcc addr ti]) ∨
     (updated = true ∧ ∃ (updAcc : AccessDescriptor) (ee : BitVec 1) (word : BitVec 64),
        updAcc.acctype = .AccessType_TTW ∧
        delta = #[descriptorReadEvent readAcc addr ti, swapReadEvent updAcc addr,
          swapWriteEvent ee word updAcc addr]))

/-- Ordered per-step actual walk events appended to `before`. -/
def WalkTrafficFrom (before : Array Event) (steps : List (Nat × Bool × Array Event)) (after : Array Event) : Prop :=
  after = steps.foldl (fun events step => events ++ step.2.2) before ∧
    ∀ step ∈ steps, WalkStepTraffic step.1 step.2.1 step.2.2

/-- Execute the existing finite topology path using the ACTUAL source body.
Each descriptor is recovered from the current image after preceding stores.
The canonical inherited prior is constructed along this same source trace. -/
theorem finite_path_trace_events {domain : QueryDomain} (spec : TopologyImageSpec domain)
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
      0 < steps ∧ steps ≤ 4 - level ∧
      S2Loop.Trace walkStop (S1WalkSource.named.body0 spec.params va .Regime_EL20 acc 64 startlevel)
        steps (alignedInput, descaddr, oldDescriptor, typ, fault, a64, s2, skl, walkaddr, current)
        initial (.ok out) other ∧
      PathPermissionAnnotation (logicalObserve spec.logicalRows) (effectiveBits spec.physicalConfig).toNat
        va spec.controls path (nativeTablePermissionProjection current.permissions) words prior ∧
      WalkLeafEndpoint spec.params config spec.controls (outputOverlayEnabled initial.regs)
        leafLevel leafPhysical leafView prior out other ∧ other.regs = initial.regs ∧
      StoreHistory spec.params (rowsFootprint spec.imageRows) initial.mem operations other.mem ∧
      ∃ traffic : List (Nat × Bool × Array Event), traffic.length = steps ∧
        WalkTrafficFrom initial.events traffic other.events ∧
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
      by decide, by omega, .done bodyCall (by rfl), ?_, ?_, registers, ?_,
      [(descaddr.address.toNat, false, #[descriptorReadEvent
        (S1ReadAccDesc.value (current.level == startlevel) (AArch64_GetVARange va) acc readBase)
        {walkaddr with paddress := descaddr}
        (S1OuterSplit.info spec.params .Regime_EL20 current {walkaddr with paddress := descaddr})])],
      rfl, ⟨?_, ?_⟩, ?_⟩
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
      annotation, meaning, tailRegs, tailHistory, tailTraffic, tailLength, ⟨tailEvents, tailSteps⟩, tailSlots⟩ :=
      finite_path_trace_events spec config va acc startlevel tail leafLevel leafLogical leafPhysical leafView
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
        WalkStepTraffic descaddr.address.toNat updated delta ∧ middle.events = initial.events ++ delta := by
      by_cases same : S1TableUpdate.word spec.params descriptor = descriptor
      · simp only [same, ↓reduceIte] at events
        exact ⟨false, _, ⟨_, _, _, readTTW, rfl, Or.inl ⟨rfl, rfl⟩⟩, by rw [events, Array.push_eq_append]; try rfl⟩
      · simp only [same, ↓reduceIte] at events
        obtain ⟨updateBase, updateTTW, updated⟩ := events
        let readAcc := S1ReadAccDesc.value (current.level == startlevel) (AArch64_GetVARange va) acc readBase
        let addr : AddressDescriptor := {walkaddr with paddress := descaddr}
        let ti := S1OuterSplit.info spec.params .Regime_EL20 current addr
        let updAcc := S1AccDescFrame.updated acc updateBase
        refine ⟨true, #[descriptorReadEvent readAcc addr ti, swapReadEvent updAcc addr,
          swapWriteEvent spec.params.ee (S1TableUpdate.word spec.params descriptor) updAcc addr],
          ⟨readAcc, addr, ti, readTTW, rfl, Or.inr ⟨rfl, updAcc, spec.params.ee,
            S1TableUpdate.word spec.params descriptor, updateTTW, rfl⟩⟩, ?_⟩
        rw [updated]
        simp only [Array.push_eq_append, Array.append_assoc]
        rfl
    obtain ⟨updated, delta, stepTraffic, middleEvents⟩ := headStep
    refine ⟨steps + 1, out, other, view.stable :: words, prior,
      tableOperations spec.params descaddr.address.toNat descriptor ++ operations,
      by omega, by omega, .next bodyCall (by rfl) trace, ?_, ?_, tailRegs.trans registers,
      history.append tailHistory, (descaddr.address.toNat, updated, delta) :: tailTraffic,
      by simp only [List.length_cons, tailLength], ⟨?_, ?_⟩, ?_⟩
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
    · intro nodup
      have fuel : 4 - level = (4 - (level + 1)) + 1 := by omega
      rw [fuel, walk_slots_table spec.logicalRows nodup va (4 - (level + 1)) level bits base descaddr view observed kind,
        List.map_cons, tailSlots nodup, slot]
termination_by 4 - level
decreasing_by omega

#print axioms finite_path_trace_events
end ArmCertWalk
