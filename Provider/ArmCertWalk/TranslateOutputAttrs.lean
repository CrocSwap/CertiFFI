import ArmCertWalk.TranslateOutputParts
import ArmCertWalk.TranslateFinishCallees

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk
open S1NormalME

private theorem normal_nc_ensures :
    Ensures (fun _ => True) (monadLift (NormalNCMemAttr ()) : SailME (FaultRecord × AddressDescriptor) MemoryAttributes)
      (fun attrs => attrs.memtype = .MemType_Normal) := by
  intro state _
  obtain ⟨attrs, other, call, normal, registers, memory, events⟩ := normal_nc_total state
  refine ⟨attrs, other, ?_, ⟨registers, memory, events⟩, normal⟩
  simp [monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, Functor.map, EStateM.map, call]

private theorem mte2_normal : S1Normality.Normal (HaveMTE2Ext ()) := by
  intro state
  exact ⟨_, state, rfl, rfl, rfl, rfl⟩

private theorem tagged_choice_normal : S1Normality.Normal (ConstrainUnpredictableBool .Unpredictable_S1CTAGGED) := by
  unfold ConstrainUnpredictableBool
  apply S1Normality.bind_normal _ _ (S1Normality.occ_normal 514)
  intro label
  exact S1EntryCalleesExtra.bool_normal label

/-- Actual output attributes remain Normal with either I/D cache query value.
The source may choose NC attributes and may update tags after its real MTE2 /
unpredictable query. No cache-enable or tag-choice pin is introduced. -/
theorem output_attrs_ensures (acc : AccessDescriptor) (next : TTWState) (instructionNC : Bool)
    (normal : next.memattrs.memtype = .MemType_Normal) :
    Ensures (fun _ => True) (TranslateOutputParts.selection .Regime_EL20 acc next instructionNC)
      (fun attrs => attrs.memtype = .MemType_Normal) := by
  unfold TranslateOutputParts.selection
  apply ite_ensures
  · intro selected
    apply bind_ensures _ _ _ _ _ normal_nc_ensures
    intro attrs attrsNormal
    exact pure_ensures _ _ _ attrsNormal
  · intro ordinary
    apply bind_ensures _ _ _ (fun _ => True)
    · repeat first
        | exact normal_pure _ _
        | exact lift_normal _ _ (S1EntryCallees.dcache_normal .Regime_EL20 (.inr rfl))
        | apply normal_ite
        | apply normal_bind
        | intro x
    · intro dataNC _
      apply ite_ensures
      · intro selected
        apply bind_ensures _ _ _ _ _ normal_nc_ensures
        intro attrs attrsNormal
        apply bind_ensures _ _ _ (fun _ => True)
        · repeat first
            | exact normal_pure _ _
            | exact lift_normal _ _ mte2_normal
            | exact lift_normal _ _ tagged_choice_normal
            | apply normal_ite
            | apply normal_bind
            | intro x
        · intro tagChoice _
          apply pure_ensures
          split <;> exact attrsNormal
      · intro selected
        exact pure_ensures _ _ _ normal

#print axioms output_attrs_ensures
end ArmCertWalk
