import ArmCertWalk.InitialWalkFacts
import Walk.S1LogicalTopology

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

/-- Pure CURRENT register/parameter geometry. No source-call result or future
walk answer occurs in these fields. Input width and starting level are data. -/
structure CurrentLayoutAt (layout : S1LogicalReference.Layout) (params : S1TTWParams)
    (va : BitVec 64) (registers : Regs) : Prop where
  start : (layout.start : Int) = rootStartLevel params
  inputBits : (layout.inputBits : Int) = AArch64_IASize params.txsz
  root : layout.root.setWidth 56 = rootBaseValue params (selectedRootTTBR registers va)

theorem CurrentLayoutAt.of_regs {layout : S1LogicalReference.Layout} {params : S1TTWParams}
    {va : BitVec 64} {before after : Regs} (current : CurrentLayoutAt layout params va before)
    (registers : after = before) : CurrentLayoutAt layout params va after := by
  rw [registers]
  exact current

theorem initial_walk_layout_total (params : S1TTWParams) (va : BitVec 64) (state : State)
    (layout : S1LogicalReference.Layout)
    (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) (tg : params.tgx = .TGx_4KB)
    (current : CurrentLayoutAt layout params va state.regs) :
    ∃ walkstate other,
      AArch64_S1InitialTTWState params va .Regime_EL20 .SS_NonSecure state =
        .ok walkstate other ∧ InitialWalkMeaning params va state.regs walkstate ∧
      walkstate.level = (layout.start : Int) ∧
      walkstate.baseaddress.address = layout.root.setWidth 56 ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨walkstate, other, call, meaning, registers, memory, events⟩ :=
    initial_walk_total params va state d128 ds tg
  exact ⟨walkstate, other, call, meaning, meaning.2.2.1.trans current.start.symm,
    meaning.1.trans current.root.symm, registers, memory, events⟩

#print axioms initial_walk_layout_total

end ArmCertWalk
