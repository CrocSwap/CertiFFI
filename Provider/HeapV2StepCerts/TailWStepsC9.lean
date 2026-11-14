-- Memory (B1 (c),): the scrub MOVZ Xd, #0 tails at 332, 334..349 (value effect Xd = 0, so x0..x17 are
-- constants at 357) and the epilogue TST x1, #7 at 350 (effect: Z <-> x1 &&& 7 = 0, so Z = 1 at 351). These steps are no
-- longer ofV steps: use tailW_k (like tailW_333 in TailWStepsC8).
import HeapV2StepCerts.TailW
set_option autoImplicit false
set_option maxRecDepth 100000
namespace HeapV2StepCerts.TailW

/-- step 332 @+0x5c MOVZ64 d2800000 (Movz64z {'Rd': 0, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_332 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (0#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 332) 332 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (0#5) (by decide) (by decide +kernel) ⟨⟩ 332 (by decide +kernel))

/-- step 334 @+0x64 MOVZ64 d2800002 (Movz64z {'Rd': 2, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_334 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (2#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 334) 334 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (2#5) (by decide) (by decide +kernel) ⟨⟩ 334 (by decide +kernel))

/-- step 335 @+0x68 MOVZ64 d2800003 (Movz64z {'Rd': 3, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_335 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (3#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 335) 335 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (3#5) (by decide) (by decide +kernel) ⟨⟩ 335 (by decide +kernel))

/-- step 336 @+0x6c MOVZ64 d2800004 (Movz64z {'Rd': 4, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_336 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (4#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 336) 336 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (4#5) (by decide) (by decide +kernel) ⟨⟩ 336 (by decide +kernel))

/-- step 337 @+0x70 MOVZ64 d2800005 (Movz64z {'Rd': 5, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_337 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (5#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 337) 337 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (5#5) (by decide) (by decide +kernel) ⟨⟩ 337 (by decide +kernel))

/-- step 338 @+0x74 MOVZ64 d2800006 (Movz64z {'Rd': 6, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_338 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (6#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 338) 338 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (6#5) (by decide) (by decide +kernel) ⟨⟩ 338 (by decide +kernel))

/-- step 339 @+0x78 MOVZ64 d2800007 (Movz64z {'Rd': 7, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_339 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (7#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 339) 339 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (7#5) (by decide) (by decide +kernel) ⟨⟩ 339 (by decide +kernel))

/-- step 340 @+0x7c MOVZ64 d2800008 (Movz64z {'Rd': 8, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_340 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (8#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 340) 340 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (8#5) (by decide) (by decide +kernel) ⟨⟩ 340 (by decide +kernel))

/-- step 341 @+0x80 MOVZ64 d2800009 (Movz64z {'Rd': 9, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_341 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (9#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 341) 341 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (9#5) (by decide) (by decide +kernel) ⟨⟩ 341 (by decide +kernel))

/-- step 342 @+0x84 MOVZ64 d280000a (Movz64z {'Rd': 10, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_342 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (10#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 342) 342 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (10#5) (by decide) (by decide +kernel) ⟨⟩ 342 (by decide +kernel))

/-- step 343 @+0x88 MOVZ64 d280000b (Movz64z {'Rd': 11, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_343 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (11#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 343) 343 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (11#5) (by decide) (by decide +kernel) ⟨⟩ 343 (by decide +kernel))

/-- step 344 @+0x8c MOVZ64 d280000c (Movz64z {'Rd': 12, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_344 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (12#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 344) 344 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (12#5) (by decide) (by decide +kernel) ⟨⟩ 344 (by decide +kernel))

/-- step 345 @+0x90 MOVZ64 d280000d (Movz64z {'Rd': 13, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_345 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (13#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 345) 345 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (13#5) (by decide) (by decide +kernel) ⟨⟩ 345 (by decide +kernel))

/-- step 346 @+0x94 MOVZ64 d280000e (Movz64z {'Rd': 14, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_346 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (14#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 346) 346 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (14#5) (by decide) (by decide +kernel) ⟨⟩ 346 (by decide +kernel))

/-- step 347 @+0x98 MOVZ64 d280000f (Movz64z {'Rd': 15, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_347 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (15#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 347) 347 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (15#5) (by decide) (by decide +kernel) ⟨⟩ 347 (by decide +kernel))

/-- step 348 @+0x9c MOVZ64 d2800010 (Movz64z {'Rd': 16, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_348 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (16#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 348) 348 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (16#5) (by decide) (by decide +kernel) ⟨⟩ 348 (by decide +kernel))

/-- step 349 @+0xa0 MOVZ64 d2800011 (Movz64z {'Rd': 17, 'imm16': 0, 'hv': 0, 'hw': 0}) -/
theorem tailW_349 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.Movz64z.selected (17#5) (0#16)) NativeEntryBodyAdapters.Movz64z.writes 698 source (source.regs._PC + 4#64) (RegBind.upds 349) 349 :=
  ClassTailWAt.holds (by decide) (Movz64z0_tailW (real := real) source (17#5) (by decide) (by decide +kernel) ⟨⟩ 349 (by decide +kernel))

/-- step 350 @+0xa4 ANDS_imm64 f240083f (AndsImm0_2 {'Rd': 31, 'Rn': 1}) -/
theorem tailW_350 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWAt real (NativeEntryBodyDispatch.AndsImm0_2.selected (1#5)) NativeEntryBodyFlag.AndsImm0_2.writes 41 source (source.regs._PC + 4#64) (RegBind.upds 350) 350 :=
  ClassTailWAt.holds (by decide) (AndsImm0_2_tailW (real := real) source (1#5) (by decide) (by decide +kernel) 350 (by decide +kernel))

end HeapV2StepCerts.TailW
