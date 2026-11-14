import Pilot.S2SwapAny
import Pilot.S2Endian
import Pilot.S2PhysFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S2SwapAnyFrame
abbrev State := SequentialState Regs oracleChoiceSource

theorem from_descriptor (ee : BitVec 1) (fault : FaultRecord) (prev next : BitVec 64)
    (acc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo) (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hTableRAM : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (hold : S2ByteMemory.DescAt s.mem addr.paddress.address.toNat (S2Endian.encode ee prev)) :
    AArch64_MemSwapTableDesc fault prev next ee acc addr ti s =
      S2SwapAny.native fault prev next (S2Endian.encode ee prev) ee acc addr ti s := by
  have hGIC : Sail.BitVec.castWidth (m := 40)
      (Sail.BitVec.extractLsb addr.paddress.address (Sail.Int.toNatChecked 55) 16) ≠ 11264#40 := by
    simpa [Sail.BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.extractLsb,
      Sail.Int.toNatChecked, GIC_BASE] using hTableRAM.1
  have hUART : Sail.BitVec.castWidth (m := 40)
      (Sail.BitVec.extractLsb addr.paddress.address (Sail.Int.toNatChecked 55) 16) ≠ 15360#40 := by
    simpa [Sail.BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.extractLsb,
      Sail.Int.toNatChecked, UART_BASE] using hTableRAM.2
  apply S2SwapAny.complete fault prev next (S2Endian.encode ee prev) ee acc addr ti s hNoRME hGIC hUART
    hTableRAM.1 hTableRAM.2 hTableRAM hold
  · simpa using hold 0 (by decide)
  · exact hold 1 (by decide)
  · exact hold 2 (by decide)
  · exact hold 3 (by decide)
  · exact hold 4 (by decide)
  · exact hold 5 (by decide)
  · exact hold 6 (by decide)
  · exact hold 7 (by decide)

def Effect (ee : BitVec 1) (fault : FaultRecord) (next : BitVec 64) (s : State) (a : Nat) :
    EStateM.Result (Sail.Error exception) State (FaultRecord × BitVec 64) → Prop
  | .ok (fault', returned) s' =>
      fault' = fault ∧ returned = next ∧ s'.regs = s.regs ∧
        s'.mem = S2ByteMemory.store s.mem a (S2Endian.encode ee next)
  | .error _ _ => False

theorem effect (ee : BitVec 1) (fault : FaultRecord) (prev next : BitVec 64)
    (acc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo) (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hTableRAM : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (hold : S2ByteMemory.DescAt s.mem addr.paddress.address.toNat (S2Endian.encode ee prev)) :
    Effect ee fault next s addr.paddress.address.toNat
      (AArch64_MemSwapTableDesc fault prev next ee acc addr ti s) := by
  rw [from_descriptor ee fault prev next acc addr ti s hNoRME hTableRAM hold]
  delta S2SwapAny.native
  unfold Sail.BitVec.length
  -- Definitional normalization repairs closed width arithmetic before simp.
  -- The resulting target and all subsequent equalities are kernel checked.
  run_tac Lean.Elab.Tactic.liftMetaTactic fun g => g.withContext do
    let t ← g.getType
    let t ← Lean.Meta.transform t (pre := fun e => do
      if e.isAppOf ``Nat.div.go || e.isAppOf ``Sail.Int.toNatChecked then
        return .done (← Lean.Meta.withTransparency .all <| Lean.Meta.whnf e)
      return .continue)
    return [← g.change t]
  simp only [Sail.BitVec.castWidth_eq]
  dsimp
  rw [S2Bytes.join64 (S2Endian.encode ee prev)]
  by_cases hee : ee = 1#1 <;>
    simp [Effect, S2ByteMemory.store, S2Endian.encode, hee, S2Endian.reverse_involutive] <;> rfl

theorem total (ee : BitVec 1) (fault : FaultRecord) (prev next : BitVec 64)
    (acc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo) (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hTableRAM : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (hold : S2ByteMemory.DescAt s.mem addr.paddress.address.toNat (S2Endian.encode ee prev)) :
    ∃ s' : State,
      AArch64_MemSwapTableDesc fault prev next ee acc addr ti s = .ok (fault, next) s' ∧
      s'.regs = s.regs ∧ s'.mem = S2ByteMemory.store s.mem addr.paddress.address.toNat (S2Endian.encode ee next) := by
  have he := effect ee fault prev next acc addr ti s hNoRME hTableRAM hold
  cases hr : AArch64_MemSwapTableDesc fault prev next ee acc addr ti s with
  | error err t => simp only [hr, Effect] at he
  | ok pair t =>
    rcases pair with ⟨f, d⟩
    simp only [hr, Effect] at he
    rcases he with ⟨hf, hd, hregs, hmem⟩
    subst f; subst d
    exact ⟨t, rfl, hregs, hmem⟩

#print axioms total

#print axioms effect
end S2SwapAnyFrame
