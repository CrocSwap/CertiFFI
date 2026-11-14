import ArmCertWalk.LeafPrepareFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

structure LeafPreparedMeaning (current : TTWState) (level : Nat) (descriptor : BitVec 64)
    (prepared : TTWState) : Prop where
  istable : prepared.istable = false
  level_eq : prepared.level = (level : Int)
  base : prepared.baseaddress.address = S1LogicalReference.leafBase level descriptor
  nonsecure : prepared.baseaddress.paspace = .PAS_NonSecure

theorem leaf_prefix_total (current : TTWState) (level : Nat) (s2 : Bool)
    (params : S1TTWParams) (descriptor : BitVec 64) (state : State)
    (nonsecure : current.baseaddress.paspace = .PAS_NonSecure)
    (currentLevel : current.level = (level : Int)) (valid : level ≤ 3)
    (aie : params.aie = 0#1) (d128 : params.d128 = 0#1) (ds : params.ds = 0#1)
    (tg : params.tgx = .TGx_4KB) :
    ∃ prepared other, LeafNextStages.beforeAttrs current s2 params descriptor state =
      .ok (prepared, leafAttributeIndex descriptor, leafShareability descriptor) other ∧
      LeafPreparedMeaning current level descriptor prepared ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨seed, base, first, seedsCall, seedsRegs, seedsMem, seedsEvents⟩ :=
    LeafNextStages.seeds_total state
  have baseCall : AArch64_LeafBase descriptor params.d128 params.ds params.tgx current.level first =
      .ok (S1LogicalReference.leafBase level descriptor) first := by
    rw [d128, ds, tg, currentLevel]
    exact leaf_base_canonical_total descriptor level first valid
  obtain ⟨other, prepareCall, registers, memory, events⟩ :=
    leaf_prepare_total current s2 params descriptor seed base (S1LogicalReference.leafBase level descriptor)
      first nonsecure aie d128 ds
  refine ⟨leafPrepared current seed base (S1LogicalReference.leafBase level descriptor), other, ?_, ?_, registers.trans seedsRegs, memory.trans seedsMem, events.trans seedsEvents⟩
  · simp only [LeafNextStages.beforeAttrs, Bind.bind, EStateM.bind, seedsCall, baseCall, prepareCall]
  · exact ⟨rfl, currentLevel, rfl, rfl⟩

#print axioms leaf_prefix_total
end ArmCertWalk
