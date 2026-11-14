import Pilot.S2Fetch
import Pilot.S2TableRAM
import Pilot.S2ByteMemory
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S2FetchFrame
abbrev State := SequentialState Regs oracleChoiceSource
theorem from_descriptor (ee : BitVec 1) (fault : FaultRecord) (data : BitVec 64)
    (acc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo) (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hTableRAM : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (hold : S2ByteMemory.DescAt s.mem addr.paddress.address.toNat data) :
    FetchDescriptor ee addr acc fault 64 ti s =
      S2Fetch.native ee addr acc fault ti data s := by
  have hGIC : Sail.BitVec.castWidth (m := 40)
      (Sail.BitVec.extractLsb addr.paddress.address (Sail.Int.toNatChecked 55) 16) ≠ 11264#40 := by
    simpa [Sail.BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.extractLsb,
      Sail.Int.toNatChecked, GIC_BASE] using hTableRAM.1
  have hUART : Sail.BitVec.castWidth (m := 40)
      (Sail.BitVec.extractLsb addr.paddress.address (Sail.Int.toNatChecked 55) 16) ≠ 15360#40 := by
    simpa [Sail.BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.extractLsb,
      Sail.Int.toNatChecked, UART_BASE] using hTableRAM.2
  apply S2Fetch.complete ee addr acc fault ti data s hNoRME hGIC hUART
  · simpa using hold 0 (by decide)
  · exact hold 1 (by decide)
  · exact hold 2 (by decide)
  · exact hold 3 (by decide)
  · exact hold 4 (by decide)
  · exact hold 5 (by decide)
  · exact hold 6 (by decide)
  · exact hold 7 (by decide)

def decoded (ee : BitVec 1) (data : BitVec 64) : BitVec 64 :=
  if ee == 1#1 then reverse_endianness data else data
def Effect (ee : BitVec 1) (fault : FaultRecord) (data : BitVec 64) (s : State) :
    EStateM.Result (Sail.Error exception) State (FaultRecord × BitVec 64) → Prop
  | .ok (f, d) t => f = fault ∧ d = decoded ee data ∧ t.regs = s.regs ∧ t.mem = s.mem
  | .error _ _ => False
theorem effect (ee : BitVec 1) (fault : FaultRecord) (data : BitVec 64)
    (acc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo) (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hTableRAM : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (hold : S2ByteMemory.DescAt s.mem addr.paddress.address.toNat data) :
    Effect ee fault data s (FetchDescriptor ee addr acc fault 64 ti s) := by
  rw [from_descriptor ee fault data acc addr ti s hNoRME hTableRAM hold]
  delta S2Fetch.native
  run_tac Lean.Elab.Tactic.liftMetaTactic fun g => g.withContext do
    let t ← g.getType
    let t ← Lean.Meta.transform t (pre := fun e => do
      if e.isAppOf ``Nat.div.go || e.isAppOf ``Sail.Int.toNatChecked then
        return .done (← Lean.Meta.withTransparency .all <| Lean.Meta.whnf e)
      return .continue)
    return [← g.change t]
  simp [Effect, decoded]
theorem total (ee : BitVec 1) (fault : FaultRecord) (data : BitVec 64)
    (acc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo) (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hTableRAM : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (hold : S2ByteMemory.DescAt s.mem addr.paddress.address.toNat data) :
    ∃ t : State, FetchDescriptor ee addr acc fault 64 ti s = .ok (fault, decoded ee data) t ∧
      t.regs = s.regs ∧ t.mem = s.mem := by
  have he := effect ee fault data acc addr ti s hNoRME hTableRAM hold
  cases hr : FetchDescriptor ee addr acc fault 64 ti s with
  | error err t => simp only [hr, Effect] at he
  | ok pair t =>
    rcases pair with ⟨f, d⟩
    simp only [hr, Effect] at he
    rcases he with ⟨hf, hd, hregs, hmem⟩
    subst f; subst d
    exact ⟨t, rfl, hregs, hmem⟩
#print axioms total

#print axioms effect
end S2FetchFrame
