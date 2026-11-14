import ArmCertWalk.TranslateEntryGuards
import ArmCertTranslateModel.HostWalkInputs

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

def currentRawTxszFault (regs : Regs) : Bool :=
  if ((_get_TCR_EL2_Type_T0SZ (regs.bank_BitVec_64 .TCR_EL2)).toNat : Int) < 16 then regs.FeatureImpl[71] else false

theorem raw_txsz_fault_of_shape (regs : Regs) (params : S1TTWParams)
    (shape : HostLower.Shape (regs.bank_BitVec_64 .TCR_EL2) (regs.bank_BitVec_64 .MAIR_EL2) params) :
    sourceTxszFault regs params = currentRawTxszFault regs := by
  obtain ⟨_, _, _, _, _, _, txsz, _⟩ := shape
  simp only [sourceTxszFault, currentRawTxszFault, txsz]

/-- Normality of the actual ignored wrapper seed, with its occurrence effects
retained. No complete state equality is asserted. -/
theorem params_draw_normal (n : Nat) : S1Normality.Normal (do
    undefined_S1TTWParams (← occLabel n) ()) := by
  apply S1Normality.bind_normal _ _ (S1Normality.occ_normal n)
  intro label
  exact undefined_params_normal label

theorem prefix_access_draw {R : Type} (n : Nat) : S1NormalME.Normal (fun _ => True) (do
    undefined_AccessDescriptor (← occLabel n) () : SailME R AccessDescriptor) := by
  apply S1NormalME.normal_bind
  · exact S1NormalME.lift_normal _ _ (S1Normality.occ_normal n)
  · intro label
    exact S1NormalME.lift_normal _ _ (undefined_access_normal label)

theorem prefix_tlbline_draw {R : Type} (n : Nat) : S1NormalME.Normal (fun _ => True) (do
    undefined_TLBLine (← occLabel n) () : SailME R TLBLine) := by
  apply S1NormalME.normal_bind
  · exact S1NormalME.lift_normal _ _ (S1Normality.occ_normal n)
  · intro label
    exact S1NormalME.lift_normal _ _ (undefined_tlbline_normal label)

theorem prefix_walk_draw {R : Type} (n : Nat) : S1NormalME.Normal (fun _ => True) (do
    undefined_TTWState (← occLabel n) () : SailME R TTWState) := by
  apply S1NormalME.normal_bind
  · exact S1NormalME.lift_normal _ _ (S1Normality.occ_normal n)
  · intro label
    exact S1NormalME.lift_normal _ _ (S1Normality.walk_normal label)

theorem prefix_bits128_draw {R : Type} (n : Nat) : S1NormalME.Normal (fun _ => True) (do
    undefined_bitvector_at (← occLabel n) 128 : SailME R (BitVec 128)) := by
  apply S1NormalME.normal_bind
  · exact S1NormalME.lift_normal _ _ (S1Normality.occ_normal n)
  · intro label
    exact S1NormalME.lift_normal _ _ (S1Normality.bits_normal 128 label)

#print axioms raw_txsz_fault_of_shape
#print axioms params_draw_normal
#print axioms prefix_access_draw
#print axioms prefix_tlbline_draw
#print axioms prefix_walk_draw
#print axioms prefix_bits128_draw
end ArmCertWalk
