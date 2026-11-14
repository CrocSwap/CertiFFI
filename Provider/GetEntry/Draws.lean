import GetEntry.PrefixCallees
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 150000
namespace S1EntryDraws
open S1NormalME
abbrev P : Regs → Prop := fun _ => True

theorem bool_draw {R : Type} (n : Nat) : Normal P (do
    undefined_bool_at (← occLabel n) () : SailME R Bool) := by
  apply normal_bind
  · exact lift_normal _ _ (S1Normality.occ_normal n)
  · intro label
    exact lift_normal _ _ (S1EntryCalleesExtra.bool_normal label)

theorem context_draw {R : Type} (n : Nat) : Normal P (do
    undefined_TLBContext (← occLabel n) () : SailME R TLBContext) := by
  apply normal_bind
  · exact lift_normal _ _ (S1Normality.occ_normal n)
  · intro label
    exact lift_normal _ _ (S1EntryCalleesExtra.context_normal label)

theorem record_draw {R : Type} (n : Nat) : Normal P (do
    undefined_TLBRecord (← occLabel n) () : SailME R TLBRecord) := by
  apply normal_bind
  · exact lift_normal _ _ (S1Normality.occ_normal n)
  · intro label
    exact lift_normal _ _ (S1EntryCalleesExtra.record_normal label)

theorem bits_draw {R : Type} (n : Nat) : Normal P (do
    (Sail.BitVec.castWidth (m := 64) <$> undefined_bitvector_at (← occLabel n)
      (Sail.Int.toNatChecked (64 : Int))) : SailME R (BitVec 64)) := by
  apply normal_bind
  · exact lift_normal _ _ (S1Normality.occ_normal n)
  · intro label
    apply normal_map
    exact lift_normal _ _ (S1Normality.bits_normal 64 label)

theorem address_normal (label : ChoiceLabel) :
    S1Normality.Normal (undefined_AddressDescriptor label ()) := by
  intro s
  exact S1Unknowns.undefined_address_total label s

theorem address_draw {R : Type} (n : Nat) : Normal P (do
    undefined_AddressDescriptor (← occLabel n) () : SailME R AddressDescriptor) := by
  apply normal_bind
  · exact lift_normal _ _ (S1Normality.occ_normal n)
  · intro label
    exact lift_normal _ _ (address_normal label)

theorem type_draw {R : Type} (n : Nat) : Normal P (do
    undefined_DescriptorType (← occLabel n) () : SailME R DescriptorType) := by
  apply normal_bind
  · exact lift_normal _ _ (S1Normality.occ_normal n)
  · intro label
    exact lift_normal _ _ (S1EntryCalleesExtra.descriptor_type_normal label)
#print axioms bool_draw
#print axioms record_draw
#print axioms bits_draw
#print axioms type_draw

theorem epd_flag {R : Type} (regime : Regime) (va : BitVec 64)
    (hregime : S1LeafBoth.Regimes regime) : Normal P (do
      let d ← AArch64_S1EPD regime va
      pure (d == 1#1) : SailME R Bool) := by
  apply normal_bind
  · exact lift_normal _ _ (S1EntryCallees.epd_normal regime va hregime)
  · intro d
    exact normal_pure _ _
#print axioms epd_flag

end S1EntryDraws
