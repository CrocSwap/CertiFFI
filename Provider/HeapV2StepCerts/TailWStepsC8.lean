-- Memory: the MOVZ x1, #0 tail at step 333 with its value effect (x1 = 0, carried to the
-- epilogue TST x1 at step 350). Step 333 is no longer an ofV step: use tailW_333.
import HeapV2StepCerts.TailW
set_option autoImplicit false
set_option maxRecDepth 100000
namespace HeapV2StepCerts.TailW

/-- step 333 @+0x60 MOVZ64 d2800001 (Movz64z {'Rd': 1, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_333 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (1#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 333) 333 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (1#5) (by decide) (by decide +kernel) ⟨⟩ 333 (by decide +kernel))

#print axioms tailW_333
end HeapV2StepCerts.TailW
