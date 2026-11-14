import Bridge.CruxGenGuarded.SpecPmu
import Bridge.CruxGen
import Bridge.CruxGenGuarded.QuietTransport
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! GENERATED from actual metadata/dispatch proof spine. The E20
input is about ONE actual hook successor and must be constructed internally
from its actual hook law. No global frame/update function is used. -/

def actionState : BitVec 32 → NativeState → Int → NativeState :=
fun w afterSpec K =>
  {
    regs :=
      { gpr := afterSpec.regs.gpr, __emulator_termination_opcode := afterSpec.regs.__emulator_termination_opcode,
        PMEVCNTSVR_EL1 := afterSpec.regs.PMEVCNTSVR_EL1, SPESampleCounter := afterSpec.regs.SPESampleCounter,
        SPERecordData := afterSpec.regs.SPERecordData, SP_EL3 := afterSpec.regs.SP_EL3, SP_EL2 := afterSpec.regs.SP_EL2,
        SP_EL1 := afterSpec.regs.SP_EL1, SP_EL0 := afterSpec.regs.SP_EL0,
        __mpam_vpmr_max := afterSpec.regs.__mpam_vpmr_max, __BranchTaken := Bool.false,
        Branchtypetaken := afterSpec.regs.Branchtypetaken, __ThisInstrEnc := ArmFull.__InstrEnc.__A64,
        __SPE_LFSR := afterSpec.regs.__SPE_LFSR, SPESampleOpType := afterSpec.regs.SPESampleOpType,
        TSTATE := afterSpec.regs.TSTATE, FPSR := afterSpec.regs.FPSR, FPCR := afterSpec.regs.FPCR,
        _ZT0 := afterSpec.regs._ZT0, _ZA := afterSpec.regs._ZA, _FFR := afterSpec.regs._FFR, _P := afterSpec.regs._P,
        _Z := afterSpec.regs._Z, BTypeCompatible := afterSpec.regs.BTypeCompatible,
        BTypeNext := afterSpec.regs.BTypeNext, RC := afterSpec.regs.RC, PhysicalCount := afterSpec.regs.PhysicalCount,
        _PC := afterSpec.regs._PC, ShouldAdvanceSS := afterSpec.regs.ShouldAdvanceSS,
        ShouldAdvanceIT := afterSpec.regs.ShouldAdvanceIT, PSTATE := afterSpec.regs.PSTATE,
        PMULastThresholdValue := afterSpec.regs.PMULastThresholdValue,
        PMUEventAccumulator := afterSpec.regs.PMUEventAccumulator,
        VariantImplemented := afterSpec.regs.VariantImplemented, FeatureImpl := afterSpec.regs.FeatureImpl,
        bank_BitVec_32 := afterSpec.regs.bank_BitVec_32.set ArmFull.Bank_BitVec_32.__ThisInstr w,
        bank_Vector_BitVec_32_16 := afterSpec.regs.bank_Vector_BitVec_32_16,
        bank_Vector_BitVec_32_4 := afterSpec.regs.bank_Vector_BitVec_32_4,
        bank_Vector_BitVec_64_32 := afterSpec.regs.bank_Vector_BitVec_64_32,
        bank_BitVec_64 := afterSpec.regs.bank_BitVec_64,
        bank_Vector_BitVec_64_16 := afterSpec.regs.bank_Vector_BitVec_64_16,
        bank_Vector_BitVec_64_4 := afterSpec.regs.bank_Vector_BitVec_64_4,
        bank_Vector_BitVec_32_31 := afterSpec.regs.bank_Vector_BitVec_32_31,
        bank_Bool := afterSpec.regs.bank_Bool.set ArmFull.Bank_Bool.__ExclusiveMonitorSet Bool.false,
        bank_Int := afterSpec.regs.bank_Int.set ArmFull.Bank_Int.SEE K, bank_BitVec_1 := afterSpec.regs.bank_BitVec_1,
        bank_BitVec_56 := afterSpec.regs.bank_BitVec_56, bank_BitVec_16 := afterSpec.regs.bank_BitVec_16,
        bank_BitVec_4 := afterSpec.regs.bank_BitVec_4.set ArmFull.Bank_BitVec_4.__currentCond (BitVec.ofNat 4 14),
        bank_BitVec_128 := afterSpec.regs.bank_BitVec_128, bank_Vector_Bool_32 := afterSpec.regs.bank_Vector_Bool_32,
        bank_Vector_BitVec_64_64 := afterSpec.regs.bank_Vector_BitVec_64_64,
        bank_Option_InterruptID := afterSpec.regs.bank_Option_InterruptID,
        bank_BitVec_8 := afterSpec.regs.bank_BitVec_8, bank_BitVec_2 := afterSpec.regs.bank_BitVec_2,
        bank_Vector_BitVec_64_7 := afterSpec.regs.bank_Vector_BitVec_64_7, bank_Signal := afterSpec.regs.bank_Signal },
    choiceState :=
      ArmBridge.CruxCore.resCS
        {
          regs :=
            { gpr := afterSpec.regs.gpr, __emulator_termination_opcode := afterSpec.regs.__emulator_termination_opcode,
              PMEVCNTSVR_EL1 := afterSpec.regs.PMEVCNTSVR_EL1, SPESampleCounter := afterSpec.regs.SPESampleCounter,
              SPERecordData := afterSpec.regs.SPERecordData, SP_EL3 := afterSpec.regs.SP_EL3,
              SP_EL2 := afterSpec.regs.SP_EL2, SP_EL1 := afterSpec.regs.SP_EL1, SP_EL0 := afterSpec.regs.SP_EL0,
              __mpam_vpmr_max := afterSpec.regs.__mpam_vpmr_max, __BranchTaken := Bool.false,
              Branchtypetaken := afterSpec.regs.Branchtypetaken, __ThisInstrEnc := ArmFull.__InstrEnc.__A64,
              __SPE_LFSR := afterSpec.regs.__SPE_LFSR, SPESampleOpType := afterSpec.regs.SPESampleOpType,
              TSTATE := afterSpec.regs.TSTATE, FPSR := afterSpec.regs.FPSR, FPCR := afterSpec.regs.FPCR,
              _ZT0 := afterSpec.regs._ZT0, _ZA := afterSpec.regs._ZA, _FFR := afterSpec.regs._FFR,
              _P := afterSpec.regs._P, _Z := afterSpec.regs._Z, BTypeCompatible := afterSpec.regs.BTypeCompatible,
              BTypeNext := afterSpec.regs.BTypeNext, RC := afterSpec.regs.RC,
              PhysicalCount := afterSpec.regs.PhysicalCount, _PC := afterSpec.regs._PC,
              ShouldAdvanceSS := afterSpec.regs.ShouldAdvanceSS, ShouldAdvanceIT := afterSpec.regs.ShouldAdvanceIT,
              PSTATE := afterSpec.regs.PSTATE, PMULastThresholdValue := afterSpec.regs.PMULastThresholdValue,
              PMUEventAccumulator := afterSpec.regs.PMUEventAccumulator,
              VariantImplemented := afterSpec.regs.VariantImplemented, FeatureImpl := afterSpec.regs.FeatureImpl,
              bank_BitVec_32 := afterSpec.regs.bank_BitVec_32.set ArmFull.Bank_BitVec_32.__ThisInstr w,
              bank_Vector_BitVec_32_16 := afterSpec.regs.bank_Vector_BitVec_32_16,
              bank_Vector_BitVec_32_4 := afterSpec.regs.bank_Vector_BitVec_32_4,
              bank_Vector_BitVec_64_32 := afterSpec.regs.bank_Vector_BitVec_64_32,
              bank_BitVec_64 := afterSpec.regs.bank_BitVec_64,
              bank_Vector_BitVec_64_16 := afterSpec.regs.bank_Vector_BitVec_64_16,
              bank_Vector_BitVec_64_4 := afterSpec.regs.bank_Vector_BitVec_64_4,
              bank_Vector_BitVec_32_31 := afterSpec.regs.bank_Vector_BitVec_32_31,
              bank_Bool := afterSpec.regs.bank_Bool.set ArmFull.Bank_Bool.__ExclusiveMonitorSet Bool.false,
              bank_Int := afterSpec.regs.bank_Int, bank_BitVec_1 := afterSpec.regs.bank_BitVec_1,
              bank_BitVec_56 := afterSpec.regs.bank_BitVec_56, bank_BitVec_16 := afterSpec.regs.bank_BitVec_16,
              bank_BitVec_4 := afterSpec.regs.bank_BitVec_4.set ArmFull.Bank_BitVec_4.__currentCond (BitVec.ofNat 4 14),
              bank_BitVec_128 := afterSpec.regs.bank_BitVec_128,
              bank_Vector_Bool_32 := afterSpec.regs.bank_Vector_Bool_32,
              bank_Vector_BitVec_64_64 := afterSpec.regs.bank_Vector_BitVec_64_64,
              bank_Option_InterruptID := afterSpec.regs.bank_Option_InterruptID,
              bank_BitVec_8 := afterSpec.regs.bank_BitVec_8, bank_BitVec_2 := afterSpec.regs.bank_BitVec_2,
              bank_Vector_BitVec_64_7 := afterSpec.regs.bank_Vector_BitVec_64_7,
              bank_Signal := afterSpec.regs.bank_Signal },
          choiceState := afterSpec.choiceState,
          choiceOcc := afterSpec.choiceOcc.insert 7631 (HAdd.hAdd (afterSpec.choiceOcc.getD 7631 0) 1),
          mem := afterSpec.mem, tags := afterSpec.tags, cycleCount := afterSpec.cycleCount,
          sailOutput := afterSpec.sailOutput, events := afterSpec.events }
        (ArmFull.Functions.SPEPreExecution Unit.unit
          {
            regs :=
              { gpr := afterSpec.regs.gpr,
                __emulator_termination_opcode := afterSpec.regs.__emulator_termination_opcode,
                PMEVCNTSVR_EL1 := afterSpec.regs.PMEVCNTSVR_EL1, SPESampleCounter := afterSpec.regs.SPESampleCounter,
                SPERecordData := afterSpec.regs.SPERecordData, SP_EL3 := afterSpec.regs.SP_EL3,
                SP_EL2 := afterSpec.regs.SP_EL2, SP_EL1 := afterSpec.regs.SP_EL1, SP_EL0 := afterSpec.regs.SP_EL0,
                __mpam_vpmr_max := afterSpec.regs.__mpam_vpmr_max, __BranchTaken := Bool.false,
                Branchtypetaken := afterSpec.regs.Branchtypetaken, __ThisInstrEnc := ArmFull.__InstrEnc.__A64,
                __SPE_LFSR := afterSpec.regs.__SPE_LFSR, SPESampleOpType := afterSpec.regs.SPESampleOpType,
                TSTATE := afterSpec.regs.TSTATE, FPSR := afterSpec.regs.FPSR, FPCR := afterSpec.regs.FPCR,
                _ZT0 := afterSpec.regs._ZT0, _ZA := afterSpec.regs._ZA, _FFR := afterSpec.regs._FFR,
                _P := afterSpec.regs._P, _Z := afterSpec.regs._Z, BTypeCompatible := afterSpec.regs.BTypeCompatible,
                BTypeNext := afterSpec.regs.BTypeNext, RC := afterSpec.regs.RC,
                PhysicalCount := afterSpec.regs.PhysicalCount, _PC := afterSpec.regs._PC,
                ShouldAdvanceSS := afterSpec.regs.ShouldAdvanceSS, ShouldAdvanceIT := afterSpec.regs.ShouldAdvanceIT,
                PSTATE := afterSpec.regs.PSTATE, PMULastThresholdValue := afterSpec.regs.PMULastThresholdValue,
                PMUEventAccumulator := afterSpec.regs.PMUEventAccumulator,
                VariantImplemented := afterSpec.regs.VariantImplemented, FeatureImpl := afterSpec.regs.FeatureImpl,
                bank_BitVec_32 := afterSpec.regs.bank_BitVec_32.set ArmFull.Bank_BitVec_32.__ThisInstr w,
                bank_Vector_BitVec_32_16 := afterSpec.regs.bank_Vector_BitVec_32_16,
                bank_Vector_BitVec_32_4 := afterSpec.regs.bank_Vector_BitVec_32_4,
                bank_Vector_BitVec_64_32 := afterSpec.regs.bank_Vector_BitVec_64_32,
                bank_BitVec_64 := afterSpec.regs.bank_BitVec_64,
                bank_Vector_BitVec_64_16 := afterSpec.regs.bank_Vector_BitVec_64_16,
                bank_Vector_BitVec_64_4 := afterSpec.regs.bank_Vector_BitVec_64_4,
                bank_Vector_BitVec_32_31 := afterSpec.regs.bank_Vector_BitVec_32_31,
                bank_Bool := afterSpec.regs.bank_Bool.set ArmFull.Bank_Bool.__ExclusiveMonitorSet Bool.false,
                bank_Int := afterSpec.regs.bank_Int, bank_BitVec_1 := afterSpec.regs.bank_BitVec_1,
                bank_BitVec_56 := afterSpec.regs.bank_BitVec_56, bank_BitVec_16 := afterSpec.regs.bank_BitVec_16,
                bank_BitVec_4 :=
                  afterSpec.regs.bank_BitVec_4.set ArmFull.Bank_BitVec_4.__currentCond (BitVec.ofNat 4 14),
                bank_BitVec_128 := afterSpec.regs.bank_BitVec_128,
                bank_Vector_Bool_32 := afterSpec.regs.bank_Vector_Bool_32,
                bank_Vector_BitVec_64_64 := afterSpec.regs.bank_Vector_BitVec_64_64,
                bank_Option_InterruptID := afterSpec.regs.bank_Option_InterruptID,
                bank_BitVec_8 := afterSpec.regs.bank_BitVec_8, bank_BitVec_2 := afterSpec.regs.bank_BitVec_2,
                bank_Vector_BitVec_64_7 := afterSpec.regs.bank_Vector_BitVec_64_7,
                bank_Signal := afterSpec.regs.bank_Signal },
            choiceState := afterSpec.choiceState,
            choiceOcc := afterSpec.choiceOcc.insert 7631 (HAdd.hAdd (afterSpec.choiceOcc.getD 7631 0) 1),
            mem := afterSpec.mem, tags := afterSpec.tags, cycleCount := afterSpec.cycleCount,
            sailOutput := afterSpec.sailOutput, events := afterSpec.events }),
    choiceOcc :=
      ArmBridge.CruxCore.resCO
        {
          regs :=
            { gpr := afterSpec.regs.gpr, __emulator_termination_opcode := afterSpec.regs.__emulator_termination_opcode,
              PMEVCNTSVR_EL1 := afterSpec.regs.PMEVCNTSVR_EL1, SPESampleCounter := afterSpec.regs.SPESampleCounter,
              SPERecordData := afterSpec.regs.SPERecordData, SP_EL3 := afterSpec.regs.SP_EL3,
              SP_EL2 := afterSpec.regs.SP_EL2, SP_EL1 := afterSpec.regs.SP_EL1, SP_EL0 := afterSpec.regs.SP_EL0,
              __mpam_vpmr_max := afterSpec.regs.__mpam_vpmr_max, __BranchTaken := Bool.false,
              Branchtypetaken := afterSpec.regs.Branchtypetaken, __ThisInstrEnc := ArmFull.__InstrEnc.__A64,
              __SPE_LFSR := afterSpec.regs.__SPE_LFSR, SPESampleOpType := afterSpec.regs.SPESampleOpType,
              TSTATE := afterSpec.regs.TSTATE, FPSR := afterSpec.regs.FPSR, FPCR := afterSpec.regs.FPCR,
              _ZT0 := afterSpec.regs._ZT0, _ZA := afterSpec.regs._ZA, _FFR := afterSpec.regs._FFR,
              _P := afterSpec.regs._P, _Z := afterSpec.regs._Z, BTypeCompatible := afterSpec.regs.BTypeCompatible,
              BTypeNext := afterSpec.regs.BTypeNext, RC := afterSpec.regs.RC,
              PhysicalCount := afterSpec.regs.PhysicalCount, _PC := afterSpec.regs._PC,
              ShouldAdvanceSS := afterSpec.regs.ShouldAdvanceSS, ShouldAdvanceIT := afterSpec.regs.ShouldAdvanceIT,
              PSTATE := afterSpec.regs.PSTATE, PMULastThresholdValue := afterSpec.regs.PMULastThresholdValue,
              PMUEventAccumulator := afterSpec.regs.PMUEventAccumulator,
              VariantImplemented := afterSpec.regs.VariantImplemented, FeatureImpl := afterSpec.regs.FeatureImpl,
              bank_BitVec_32 := afterSpec.regs.bank_BitVec_32.set ArmFull.Bank_BitVec_32.__ThisInstr w,
              bank_Vector_BitVec_32_16 := afterSpec.regs.bank_Vector_BitVec_32_16,
              bank_Vector_BitVec_32_4 := afterSpec.regs.bank_Vector_BitVec_32_4,
              bank_Vector_BitVec_64_32 := afterSpec.regs.bank_Vector_BitVec_64_32,
              bank_BitVec_64 := afterSpec.regs.bank_BitVec_64,
              bank_Vector_BitVec_64_16 := afterSpec.regs.bank_Vector_BitVec_64_16,
              bank_Vector_BitVec_64_4 := afterSpec.regs.bank_Vector_BitVec_64_4,
              bank_Vector_BitVec_32_31 := afterSpec.regs.bank_Vector_BitVec_32_31,
              bank_Bool := afterSpec.regs.bank_Bool.set ArmFull.Bank_Bool.__ExclusiveMonitorSet Bool.false,
              bank_Int := afterSpec.regs.bank_Int, bank_BitVec_1 := afterSpec.regs.bank_BitVec_1,
              bank_BitVec_56 := afterSpec.regs.bank_BitVec_56, bank_BitVec_16 := afterSpec.regs.bank_BitVec_16,
              bank_BitVec_4 := afterSpec.regs.bank_BitVec_4.set ArmFull.Bank_BitVec_4.__currentCond (BitVec.ofNat 4 14),
              bank_BitVec_128 := afterSpec.regs.bank_BitVec_128,
              bank_Vector_Bool_32 := afterSpec.regs.bank_Vector_Bool_32,
              bank_Vector_BitVec_64_64 := afterSpec.regs.bank_Vector_BitVec_64_64,
              bank_Option_InterruptID := afterSpec.regs.bank_Option_InterruptID,
              bank_BitVec_8 := afterSpec.regs.bank_BitVec_8, bank_BitVec_2 := afterSpec.regs.bank_BitVec_2,
              bank_Vector_BitVec_64_7 := afterSpec.regs.bank_Vector_BitVec_64_7,
              bank_Signal := afterSpec.regs.bank_Signal },
          choiceState := afterSpec.choiceState,
          choiceOcc := afterSpec.choiceOcc.insert 7631 (HAdd.hAdd (afterSpec.choiceOcc.getD 7631 0) 1),
          mem := afterSpec.mem, tags := afterSpec.tags, cycleCount := afterSpec.cycleCount,
          sailOutput := afterSpec.sailOutput, events := afterSpec.events }
        (ArmFull.Functions.SPEPreExecution Unit.unit
          {
            regs :=
              { gpr := afterSpec.regs.gpr,
                __emulator_termination_opcode := afterSpec.regs.__emulator_termination_opcode,
                PMEVCNTSVR_EL1 := afterSpec.regs.PMEVCNTSVR_EL1, SPESampleCounter := afterSpec.regs.SPESampleCounter,
                SPERecordData := afterSpec.regs.SPERecordData, SP_EL3 := afterSpec.regs.SP_EL3,
                SP_EL2 := afterSpec.regs.SP_EL2, SP_EL1 := afterSpec.regs.SP_EL1, SP_EL0 := afterSpec.regs.SP_EL0,
                __mpam_vpmr_max := afterSpec.regs.__mpam_vpmr_max, __BranchTaken := Bool.false,
                Branchtypetaken := afterSpec.regs.Branchtypetaken, __ThisInstrEnc := ArmFull.__InstrEnc.__A64,
                __SPE_LFSR := afterSpec.regs.__SPE_LFSR, SPESampleOpType := afterSpec.regs.SPESampleOpType,
                TSTATE := afterSpec.regs.TSTATE, FPSR := afterSpec.regs.FPSR, FPCR := afterSpec.regs.FPCR,
                _ZT0 := afterSpec.regs._ZT0, _ZA := afterSpec.regs._ZA, _FFR := afterSpec.regs._FFR,
                _P := afterSpec.regs._P, _Z := afterSpec.regs._Z, BTypeCompatible := afterSpec.regs.BTypeCompatible,
                BTypeNext := afterSpec.regs.BTypeNext, RC := afterSpec.regs.RC,
                PhysicalCount := afterSpec.regs.PhysicalCount, _PC := afterSpec.regs._PC,
                ShouldAdvanceSS := afterSpec.regs.ShouldAdvanceSS, ShouldAdvanceIT := afterSpec.regs.ShouldAdvanceIT,
                PSTATE := afterSpec.regs.PSTATE, PMULastThresholdValue := afterSpec.regs.PMULastThresholdValue,
                PMUEventAccumulator := afterSpec.regs.PMUEventAccumulator,
                VariantImplemented := afterSpec.regs.VariantImplemented, FeatureImpl := afterSpec.regs.FeatureImpl,
                bank_BitVec_32 := afterSpec.regs.bank_BitVec_32.set ArmFull.Bank_BitVec_32.__ThisInstr w,
                bank_Vector_BitVec_32_16 := afterSpec.regs.bank_Vector_BitVec_32_16,
                bank_Vector_BitVec_32_4 := afterSpec.regs.bank_Vector_BitVec_32_4,
                bank_Vector_BitVec_64_32 := afterSpec.regs.bank_Vector_BitVec_64_32,
                bank_BitVec_64 := afterSpec.regs.bank_BitVec_64,
                bank_Vector_BitVec_64_16 := afterSpec.regs.bank_Vector_BitVec_64_16,
                bank_Vector_BitVec_64_4 := afterSpec.regs.bank_Vector_BitVec_64_4,
                bank_Vector_BitVec_32_31 := afterSpec.regs.bank_Vector_BitVec_32_31,
                bank_Bool := afterSpec.regs.bank_Bool.set ArmFull.Bank_Bool.__ExclusiveMonitorSet Bool.false,
                bank_Int := afterSpec.regs.bank_Int, bank_BitVec_1 := afterSpec.regs.bank_BitVec_1,
                bank_BitVec_56 := afterSpec.regs.bank_BitVec_56, bank_BitVec_16 := afterSpec.regs.bank_BitVec_16,
                bank_BitVec_4 :=
                  afterSpec.regs.bank_BitVec_4.set ArmFull.Bank_BitVec_4.__currentCond (BitVec.ofNat 4 14),
                bank_BitVec_128 := afterSpec.regs.bank_BitVec_128,
                bank_Vector_Bool_32 := afterSpec.regs.bank_Vector_Bool_32,
                bank_Vector_BitVec_64_64 := afterSpec.regs.bank_Vector_BitVec_64_64,
                bank_Option_InterruptID := afterSpec.regs.bank_Option_InterruptID,
                bank_BitVec_8 := afterSpec.regs.bank_BitVec_8, bank_BitVec_2 := afterSpec.regs.bank_BitVec_2,
                bank_Vector_BitVec_64_7 := afterSpec.regs.bank_Vector_BitVec_64_7,
                bank_Signal := afterSpec.regs.bank_Signal },
            choiceState := afterSpec.choiceState,
            choiceOcc := afterSpec.choiceOcc.insert 7631 (HAdd.hAdd (afterSpec.choiceOcc.getD 7631 0) 1),
            mem := afterSpec.mem, tags := afterSpec.tags, cycleCount := afterSpec.cycleCount,
            sailOutput := afterSpec.sailOutput, events := afterSpec.events }),
    mem := afterSpec.mem, tags := afterSpec.tags, cycleCount := afterSpec.cycleCount,
    sailOutput := afterSpec.sailOutput, events := afterSpec.events }

def nativeAtAction : ∀ (real : Type) [Sail.SailReal real],
    NativeState → BitVec 32 → SailM Unit → __InstrEnc → NativeState →
      EStateM.Result (Sail.Error exception) NativeState Unit :=
fun real [Sail.SailReal real] s w A enc0 afterFetch =>
  EStateM.bind.match_1
    (fun x =>
      EStateM.Result (Sail.Error ArmFull.exception)
        (Sail.ConcurrencyInterfaceV1.SequentialState ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource) Unit)
    (ArmBridge.CruxCore.tc_apply.match_1
      (fun x =>
        EStateM.Result (Sail.Error ArmFull.exception)
          (Sail.ConcurrencyInterfaceV1.SequentialState ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource)
          Unit)
      (ArmBridge.CruxCore.bind_app.match_1
        (fun x =>
          EStateM.Result (Sail.Error ArmFull.exception)
            (Sail.ConcurrencyInterfaceV1.SequentialState ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource)
            Unit)
        (ArmBridge.CruxCore.tc_apply.match_1
          (fun x =>
            EStateM.Result (Sail.Error ArmFull.exception)
              (Sail.ConcurrencyInterfaceV1.SequentialState ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource)
              Unit)
          (ArmBridge.CruxCore.bind_app.match_1
            (fun x =>
              EStateM.Result (Sail.Error ArmFull.exception)
                (Sail.ConcurrencyInterfaceV1.SequentialState ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource)
                Unit)
            (ArmBridge.CruxCore.tc_apply.match_1
              (fun x =>
                EStateM.Result (Sail.Error ArmFull.exception)
                  (Sail.ConcurrencyInterfaceV1.SequentialState ArmFull.Regs
                    Sail.ConcurrencyInterfaceV1.oracleChoiceSource)
                  Unit)
              (A afterFetch) (fun a s' => EStateM.Result.ok a s')
              (fun u s' =>
                cond (ArmFull.Functions.IsSEE u)
                  (Bind.bind (ArmFull.Functions.Halted Unit.unit) fun w__0 =>
                    cond w__0
                      (ArmFull.sailTryCatch
                        (Bind.bind (ArmFull.Functions.__DefaultCond ArmFull.__InstrEnc.__A64) fun w__1 =>
                          Bind.bind (ArmFull.Functions.__SetThisInstrDetails ArmFull.__InstrEnc.__A64 w w__1) fun __r =>
                            Bind.bind (ArmFull.readReg ArmFull.Register._PC) fun w__2 =>
                              ArmFull.Functions.__DecodeA64 (↑w__2.toNat) w)
                        fun the_exception =>
                        cond (ArmFull.Functions.IsExceptionTaken the_exception) (EStateM.pure Unit.unit)
                          (cond
                            (((ArmFull.Functions.IsSEE the_exception).or
                                  (ArmFull.Functions.IsUNDEFINED the_exception)).or
                              (ArmFull.Functions.IsUNPREDICTABLE the_exception))
                            (ArmFull.Functions.AArch64_UndefinedFault Unit.unit) (ArmFull.sailThrow the_exception)))
                      (Bind.bind (ArmFull.readReg ArmFull.Register._PC) fun w__2 =>
                        ArmFull.Functions.__DecodeA64 (↑w__2.toNat) w))
                  (ArmFull.sailThrow u) s')
              fun e s' => EStateM.Result.error e s')
            (fun a s' => ArmFull.Functions.PMUEvent ArmFull.Functions.PMU_EVENT_INST_RETIRED s') fun e s' =>
            EStateM.Result.error e s')
          (fun a s' => EStateM.Result.ok a s')
          (fun u s' =>
            cond
              (((ArmFull.Functions.IsSEE u).or (ArmFull.Functions.IsUNDEFINED u)).or
                (ArmFull.Functions.IsUNPREDICTABLE u))
              (Bind.bind (ArmFull.Functions.UsingAArch32 Unit.unit) fun w__7 =>
                cond w__7
                  (ArmFull.Functions.__InstructionExecute.match_2 (fun enc => ArmFull.SailM Unit) enc0
                    (fun x =>
                      ArmFull.Functions.UnallocatedA32_Instruction
                        (Sail.ConcurrencyInterfaceV1.oracleChoiceSource.chooseAt (Sail.Primitive.bitvector 32)
                          (Sail.ConcurrencyInterfaceV1.ChoiceLabel.site 7638)
                          (ArmBridge.CruxCore.resCS
                            {
                              regs :=
                                { gpr := s.regs.gpr,
                                  __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
                                  PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1, SPESampleCounter := s.regs.SPESampleCounter,
                                  SPERecordData := s.regs.SPERecordData, SP_EL3 := s.regs.SP_EL3,
                                  SP_EL2 := s.regs.SP_EL2, SP_EL1 := s.regs.SP_EL1, SP_EL0 := s.regs.SP_EL0,
                                  __mpam_vpmr_max := s.regs.__mpam_vpmr_max, __BranchTaken := s.regs.__BranchTaken,
                                  Branchtypetaken := s.regs.Branchtypetaken, __ThisInstrEnc := s.regs.__ThisInstrEnc,
                                  __SPE_LFSR := s.regs.__SPE_LFSR, SPESampleOpType := s.regs.SPESampleOpType,
                                  TSTATE := s.regs.TSTATE, FPSR := s.regs.FPSR, FPCR := s.regs.FPCR,
                                  _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA, _FFR := s.regs._FFR, _P := s.regs._P,
                                  _Z := s.regs._Z, BTypeCompatible := s.regs.BTypeCompatible,
                                  BTypeNext := s.regs.BTypeNext, RC := s.regs.RC, PhysicalCount := s.regs.PhysicalCount,
                                  _PC := s.regs._PC, ShouldAdvanceSS := s.regs.ShouldAdvanceSS,
                                  ShouldAdvanceIT := s.regs.ShouldAdvanceIT, PSTATE := s.regs.PSTATE,
                                  PMULastThresholdValue := s.regs.PMULastThresholdValue,
                                  PMUEventAccumulator := s.regs.PMUEventAccumulator,
                                  VariantImplemented := s.regs.VariantImplemented, FeatureImpl := s.regs.FeatureImpl,
                                  bank_BitVec_32 := s.regs.bank_BitVec_32,
                                  bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
                                  bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
                                  bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32,
                                  bank_BitVec_64 := s.regs.bank_BitVec_64,
                                  bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
                                  bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
                                  bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31,
                                  bank_Bool := s.regs.bank_Bool,
                                  bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1),
                                  bank_BitVec_1 := s.regs.bank_BitVec_1, bank_BitVec_56 := s.regs.bank_BitVec_56,
                                  bank_BitVec_16 := s.regs.bank_BitVec_16, bank_BitVec_4 := s.regs.bank_BitVec_4,
                                  bank_BitVec_128 := s.regs.bank_BitVec_128,
                                  bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32,
                                  bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
                                  bank_Option_InterruptID := s.regs.bank_Option_InterruptID,
                                  bank_BitVec_8 := s.regs.bank_BitVec_8, bank_BitVec_2 := s.regs.bank_BitVec_2,
                                  bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
                                  bank_Signal := s.regs.bank_Signal },
                              choiceState := s.choiceState, choiceOcc := s.choiceOcc, mem := s.mem, tags := s.tags,
                              cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events }
                            (ArmFull.Functions.TakePendingInterrupts
                              { take_SE := Bool.true, take_vSE := Bool.true, take_IRQ := Bool.true,
                                take_vIRQ := Bool.true, take_FIQ := Bool.true, take_vFIQ := Bool.true,
                                iesb_req :=
                                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource.chooseAt Sail.Primitive.bool
                                    ((Sail.ConcurrencyInterfaceV1.ChoiceLabel.site 7640).child 6) s.choiceState }
                              {
                                regs :=
                                  { gpr := s.regs.gpr,
                                    __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
                                    PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1,
                                    SPESampleCounter := s.regs.SPESampleCounter, SPERecordData := s.regs.SPERecordData,
                                    SP_EL3 := s.regs.SP_EL3, SP_EL2 := s.regs.SP_EL2, SP_EL1 := s.regs.SP_EL1,
                                    SP_EL0 := s.regs.SP_EL0, __mpam_vpmr_max := s.regs.__mpam_vpmr_max,
                                    __BranchTaken := s.regs.__BranchTaken, Branchtypetaken := s.regs.Branchtypetaken,
                                    __ThisInstrEnc := s.regs.__ThisInstrEnc, __SPE_LFSR := s.regs.__SPE_LFSR,
                                    SPESampleOpType := s.regs.SPESampleOpType, TSTATE := s.regs.TSTATE,
                                    FPSR := s.regs.FPSR, FPCR := s.regs.FPCR, _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA,
                                    _FFR := s.regs._FFR, _P := s.regs._P, _Z := s.regs._Z,
                                    BTypeCompatible := s.regs.BTypeCompatible, BTypeNext := s.regs.BTypeNext,
                                    RC := s.regs.RC, PhysicalCount := s.regs.PhysicalCount, _PC := s.regs._PC,
                                    ShouldAdvanceSS := s.regs.ShouldAdvanceSS,
                                    ShouldAdvanceIT := s.regs.ShouldAdvanceIT, PSTATE := s.regs.PSTATE,
                                    PMULastThresholdValue := s.regs.PMULastThresholdValue,
                                    PMUEventAccumulator := s.regs.PMUEventAccumulator,
                                    VariantImplemented := s.regs.VariantImplemented, FeatureImpl := s.regs.FeatureImpl,
                                    bank_BitVec_32 := s.regs.bank_BitVec_32,
                                    bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
                                    bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
                                    bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32,
                                    bank_BitVec_64 := s.regs.bank_BitVec_64,
                                    bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
                                    bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
                                    bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31,
                                    bank_Bool := s.regs.bank_Bool,
                                    bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1),
                                    bank_BitVec_1 := s.regs.bank_BitVec_1, bank_BitVec_56 := s.regs.bank_BitVec_56,
                                    bank_BitVec_16 := s.regs.bank_BitVec_16, bank_BitVec_4 := s.regs.bank_BitVec_4,
                                    bank_BitVec_128 := s.regs.bank_BitVec_128,
                                    bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32,
                                    bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
                                    bank_Option_InterruptID := s.regs.bank_Option_InterruptID,
                                    bank_BitVec_8 := s.regs.bank_BitVec_8, bank_BitVec_2 := s.regs.bank_BitVec_2,
                                    bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
                                    bank_Signal := s.regs.bank_Signal },
                                choiceState := s.choiceState, choiceOcc := s.choiceOcc, mem := s.mem, tags := s.tags,
                                cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events }))))
                    (fun x =>
                      ArmFull.Functions.UnallocatedT32_16_Instruction
                        (Sail.BitVec.extractLsb
                          (Sail.ConcurrencyInterfaceV1.oracleChoiceSource.chooseAt (Sail.Primitive.bitvector 32)
                            (Sail.ConcurrencyInterfaceV1.ChoiceLabel.site 7638)
                            (ArmBridge.CruxCore.resCS
                              {
                                regs :=
                                  { gpr := s.regs.gpr,
                                    __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
                                    PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1,
                                    SPESampleCounter := s.regs.SPESampleCounter, SPERecordData := s.regs.SPERecordData,
                                    SP_EL3 := s.regs.SP_EL3, SP_EL2 := s.regs.SP_EL2, SP_EL1 := s.regs.SP_EL1,
                                    SP_EL0 := s.regs.SP_EL0, __mpam_vpmr_max := s.regs.__mpam_vpmr_max,
                                    __BranchTaken := s.regs.__BranchTaken, Branchtypetaken := s.regs.Branchtypetaken,
                                    __ThisInstrEnc := s.regs.__ThisInstrEnc, __SPE_LFSR := s.regs.__SPE_LFSR,
                                    SPESampleOpType := s.regs.SPESampleOpType, TSTATE := s.regs.TSTATE,
                                    FPSR := s.regs.FPSR, FPCR := s.regs.FPCR, _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA,
                                    _FFR := s.regs._FFR, _P := s.regs._P, _Z := s.regs._Z,
                                    BTypeCompatible := s.regs.BTypeCompatible, BTypeNext := s.regs.BTypeNext,
                                    RC := s.regs.RC, PhysicalCount := s.regs.PhysicalCount, _PC := s.regs._PC,
                                    ShouldAdvanceSS := s.regs.ShouldAdvanceSS,
                                    ShouldAdvanceIT := s.regs.ShouldAdvanceIT, PSTATE := s.regs.PSTATE,
                                    PMULastThresholdValue := s.regs.PMULastThresholdValue,
                                    PMUEventAccumulator := s.regs.PMUEventAccumulator,
                                    VariantImplemented := s.regs.VariantImplemented, FeatureImpl := s.regs.FeatureImpl,
                                    bank_BitVec_32 := s.regs.bank_BitVec_32,
                                    bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
                                    bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
                                    bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32,
                                    bank_BitVec_64 := s.regs.bank_BitVec_64,
                                    bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
                                    bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
                                    bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31,
                                    bank_Bool := s.regs.bank_Bool,
                                    bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1),
                                    bank_BitVec_1 := s.regs.bank_BitVec_1, bank_BitVec_56 := s.regs.bank_BitVec_56,
                                    bank_BitVec_16 := s.regs.bank_BitVec_16, bank_BitVec_4 := s.regs.bank_BitVec_4,
                                    bank_BitVec_128 := s.regs.bank_BitVec_128,
                                    bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32,
                                    bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
                                    bank_Option_InterruptID := s.regs.bank_Option_InterruptID,
                                    bank_BitVec_8 := s.regs.bank_BitVec_8, bank_BitVec_2 := s.regs.bank_BitVec_2,
                                    bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
                                    bank_Signal := s.regs.bank_Signal },
                                choiceState := s.choiceState, choiceOcc := s.choiceOcc, mem := s.mem, tags := s.tags,
                                cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events }
                              (ArmFull.Functions.TakePendingInterrupts
                                { take_SE := Bool.true, take_vSE := Bool.true, take_IRQ := Bool.true,
                                  take_vIRQ := Bool.true, take_FIQ := Bool.true, take_vFIQ := Bool.true,
                                  iesb_req :=
                                    Sail.ConcurrencyInterfaceV1.oracleChoiceSource.chooseAt Sail.Primitive.bool
                                      ((Sail.ConcurrencyInterfaceV1.ChoiceLabel.site 7640).child 6) s.choiceState }
                                {
                                  regs :=
                                    { gpr := s.regs.gpr,
                                      __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
                                      PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1,
                                      SPESampleCounter := s.regs.SPESampleCounter,
                                      SPERecordData := s.regs.SPERecordData, SP_EL3 := s.regs.SP_EL3,
                                      SP_EL2 := s.regs.SP_EL2, SP_EL1 := s.regs.SP_EL1, SP_EL0 := s.regs.SP_EL0,
                                      __mpam_vpmr_max := s.regs.__mpam_vpmr_max, __BranchTaken := s.regs.__BranchTaken,
                                      Branchtypetaken := s.regs.Branchtypetaken,
                                      __ThisInstrEnc := s.regs.__ThisInstrEnc, __SPE_LFSR := s.regs.__SPE_LFSR,
                                      SPESampleOpType := s.regs.SPESampleOpType, TSTATE := s.regs.TSTATE,
                                      FPSR := s.regs.FPSR, FPCR := s.regs.FPCR, _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA,
                                      _FFR := s.regs._FFR, _P := s.regs._P, _Z := s.regs._Z,
                                      BTypeCompatible := s.regs.BTypeCompatible, BTypeNext := s.regs.BTypeNext,
                                      RC := s.regs.RC, PhysicalCount := s.regs.PhysicalCount, _PC := s.regs._PC,
                                      ShouldAdvanceSS := s.regs.ShouldAdvanceSS,
                                      ShouldAdvanceIT := s.regs.ShouldAdvanceIT, PSTATE := s.regs.PSTATE,
                                      PMULastThresholdValue := s.regs.PMULastThresholdValue,
                                      PMUEventAccumulator := s.regs.PMUEventAccumulator,
                                      VariantImplemented := s.regs.VariantImplemented,
                                      FeatureImpl := s.regs.FeatureImpl, bank_BitVec_32 := s.regs.bank_BitVec_32,
                                      bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
                                      bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
                                      bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32,
                                      bank_BitVec_64 := s.regs.bank_BitVec_64,
                                      bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
                                      bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
                                      bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31,
                                      bank_Bool := s.regs.bank_Bool,
                                      bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1),
                                      bank_BitVec_1 := s.regs.bank_BitVec_1, bank_BitVec_56 := s.regs.bank_BitVec_56,
                                      bank_BitVec_16 := s.regs.bank_BitVec_16, bank_BitVec_4 := s.regs.bank_BitVec_4,
                                      bank_BitVec_128 := s.regs.bank_BitVec_128,
                                      bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32,
                                      bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
                                      bank_Option_InterruptID := s.regs.bank_Option_InterruptID,
                                      bank_BitVec_8 := s.regs.bank_BitVec_8, bank_BitVec_2 := s.regs.bank_BitVec_2,
                                      bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
                                      bank_Signal := s.regs.bank_Signal },
                                  choiceState := s.choiceState, choiceOcc := s.choiceOcc, mem := s.mem, tags := s.tags,
                                  cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events })))
                          15 0))
                    (fun x =>
                      ArmFull.Functions.UnallocatedT32_32_Instruction
                        (Sail.ConcurrencyInterfaceV1.oracleChoiceSource.chooseAt (Sail.Primitive.bitvector 32)
                          (Sail.ConcurrencyInterfaceV1.ChoiceLabel.site 7638)
                          (ArmBridge.CruxCore.resCS
                            {
                              regs :=
                                { gpr := s.regs.gpr,
                                  __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
                                  PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1, SPESampleCounter := s.regs.SPESampleCounter,
                                  SPERecordData := s.regs.SPERecordData, SP_EL3 := s.regs.SP_EL3,
                                  SP_EL2 := s.regs.SP_EL2, SP_EL1 := s.regs.SP_EL1, SP_EL0 := s.regs.SP_EL0,
                                  __mpam_vpmr_max := s.regs.__mpam_vpmr_max, __BranchTaken := s.regs.__BranchTaken,
                                  Branchtypetaken := s.regs.Branchtypetaken, __ThisInstrEnc := s.regs.__ThisInstrEnc,
                                  __SPE_LFSR := s.regs.__SPE_LFSR, SPESampleOpType := s.regs.SPESampleOpType,
                                  TSTATE := s.regs.TSTATE, FPSR := s.regs.FPSR, FPCR := s.regs.FPCR,
                                  _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA, _FFR := s.regs._FFR, _P := s.regs._P,
                                  _Z := s.regs._Z, BTypeCompatible := s.regs.BTypeCompatible,
                                  BTypeNext := s.regs.BTypeNext, RC := s.regs.RC, PhysicalCount := s.regs.PhysicalCount,
                                  _PC := s.regs._PC, ShouldAdvanceSS := s.regs.ShouldAdvanceSS,
                                  ShouldAdvanceIT := s.regs.ShouldAdvanceIT, PSTATE := s.regs.PSTATE,
                                  PMULastThresholdValue := s.regs.PMULastThresholdValue,
                                  PMUEventAccumulator := s.regs.PMUEventAccumulator,
                                  VariantImplemented := s.regs.VariantImplemented, FeatureImpl := s.regs.FeatureImpl,
                                  bank_BitVec_32 := s.regs.bank_BitVec_32,
                                  bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
                                  bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
                                  bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32,
                                  bank_BitVec_64 := s.regs.bank_BitVec_64,
                                  bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
                                  bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
                                  bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31,
                                  bank_Bool := s.regs.bank_Bool,
                                  bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1),
                                  bank_BitVec_1 := s.regs.bank_BitVec_1, bank_BitVec_56 := s.regs.bank_BitVec_56,
                                  bank_BitVec_16 := s.regs.bank_BitVec_16, bank_BitVec_4 := s.regs.bank_BitVec_4,
                                  bank_BitVec_128 := s.regs.bank_BitVec_128,
                                  bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32,
                                  bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
                                  bank_Option_InterruptID := s.regs.bank_Option_InterruptID,
                                  bank_BitVec_8 := s.regs.bank_BitVec_8, bank_BitVec_2 := s.regs.bank_BitVec_2,
                                  bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
                                  bank_Signal := s.regs.bank_Signal },
                              choiceState := s.choiceState, choiceOcc := s.choiceOcc, mem := s.mem, tags := s.tags,
                              cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events }
                            (ArmFull.Functions.TakePendingInterrupts
                              { take_SE := Bool.true, take_vSE := Bool.true, take_IRQ := Bool.true,
                                take_vIRQ := Bool.true, take_FIQ := Bool.true, take_vFIQ := Bool.true,
                                iesb_req :=
                                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource.chooseAt Sail.Primitive.bool
                                    ((Sail.ConcurrencyInterfaceV1.ChoiceLabel.site 7640).child 6) s.choiceState }
                              {
                                regs :=
                                  { gpr := s.regs.gpr,
                                    __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
                                    PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1,
                                    SPESampleCounter := s.regs.SPESampleCounter, SPERecordData := s.regs.SPERecordData,
                                    SP_EL3 := s.regs.SP_EL3, SP_EL2 := s.regs.SP_EL2, SP_EL1 := s.regs.SP_EL1,
                                    SP_EL0 := s.regs.SP_EL0, __mpam_vpmr_max := s.regs.__mpam_vpmr_max,
                                    __BranchTaken := s.regs.__BranchTaken, Branchtypetaken := s.regs.Branchtypetaken,
                                    __ThisInstrEnc := s.regs.__ThisInstrEnc, __SPE_LFSR := s.regs.__SPE_LFSR,
                                    SPESampleOpType := s.regs.SPESampleOpType, TSTATE := s.regs.TSTATE,
                                    FPSR := s.regs.FPSR, FPCR := s.regs.FPCR, _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA,
                                    _FFR := s.regs._FFR, _P := s.regs._P, _Z := s.regs._Z,
                                    BTypeCompatible := s.regs.BTypeCompatible, BTypeNext := s.regs.BTypeNext,
                                    RC := s.regs.RC, PhysicalCount := s.regs.PhysicalCount, _PC := s.regs._PC,
                                    ShouldAdvanceSS := s.regs.ShouldAdvanceSS,
                                    ShouldAdvanceIT := s.regs.ShouldAdvanceIT, PSTATE := s.regs.PSTATE,
                                    PMULastThresholdValue := s.regs.PMULastThresholdValue,
                                    PMUEventAccumulator := s.regs.PMUEventAccumulator,
                                    VariantImplemented := s.regs.VariantImplemented, FeatureImpl := s.regs.FeatureImpl,
                                    bank_BitVec_32 := s.regs.bank_BitVec_32,
                                    bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
                                    bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
                                    bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32,
                                    bank_BitVec_64 := s.regs.bank_BitVec_64,
                                    bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
                                    bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
                                    bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31,
                                    bank_Bool := s.regs.bank_Bool,
                                    bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1),
                                    bank_BitVec_1 := s.regs.bank_BitVec_1, bank_BitVec_56 := s.regs.bank_BitVec_56,
                                    bank_BitVec_16 := s.regs.bank_BitVec_16, bank_BitVec_4 := s.regs.bank_BitVec_4,
                                    bank_BitVec_128 := s.regs.bank_BitVec_128,
                                    bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32,
                                    bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
                                    bank_Option_InterruptID := s.regs.bank_Option_InterruptID,
                                    bank_BitVec_8 := s.regs.bank_BitVec_8, bank_BitVec_2 := s.regs.bank_BitVec_2,
                                    bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
                                    bank_Signal := s.regs.bank_Signal },
                                choiceState := s.choiceState, choiceOcc := s.choiceOcc, mem := s.mem, tags := s.tags,
                                cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events }))))
                    fun x => ArmFull.Functions.Unreachable Unit.unit)
                  (ArmFull.Functions.AArch64_UndefinedFault Unit.unit))
              (cond (ArmFull.Functions.IsExceptionTaken u) (EStateM.pure Unit.unit) (ArmFull.sailThrow u)) s')
          fun e s' => EStateM.Result.error e s')
        (fun a s' =>
          ArmBridge.CruxCore.bind_app.match_1
            (fun x =>
              EStateM.Result (Sail.Error ArmFull.exception)
                (Sail.ConcurrencyInterfaceV1.SequentialState ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource)
                Unit)
            (ArmFull.Functions.SPEPostExecution Unit.unit s')
            (fun a s' =>
              ArmBridge.CruxCore.bind_app.match_1
                (fun x =>
                  EStateM.Result (Sail.Error ArmFull.exception)
                    (Sail.ConcurrencyInterfaceV1.SequentialState ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource)
                    Unit)
                (ArmFull.Functions.AArch64_ExecutingERETInstr Unit.unit
                  {
                    regs :=
                      { gpr := s'.regs.gpr, __emulator_termination_opcode := s'.regs.__emulator_termination_opcode,
                        PMEVCNTSVR_EL1 := s'.regs.PMEVCNTSVR_EL1, SPESampleCounter := s'.regs.SPESampleCounter,
                        SPERecordData := s'.regs.SPERecordData, SP_EL3 := s'.regs.SP_EL3, SP_EL2 := s'.regs.SP_EL2,
                        SP_EL1 := s'.regs.SP_EL1, SP_EL0 := s'.regs.SP_EL0, __mpam_vpmr_max := s'.regs.__mpam_vpmr_max,
                        __BranchTaken := s'.regs.__BranchTaken, Branchtypetaken := s'.regs.Branchtypetaken,
                        __ThisInstrEnc := s'.regs.__ThisInstrEnc, __SPE_LFSR := s'.regs.__SPE_LFSR,
                        SPESampleOpType := s'.regs.SPESampleOpType, TSTATE := s'.regs.TSTATE, FPSR := s'.regs.FPSR,
                        FPCR := s'.regs.FPCR, _ZT0 := s'.regs._ZT0, _ZA := s'.regs._ZA, _FFR := s'.regs._FFR,
                        _P := s'.regs._P, _Z := s'.regs._Z, BTypeCompatible := s'.regs.BTypeCompatible,
                        BTypeNext := s'.regs.BTypeNext, RC := s'.regs.RC, PhysicalCount := s'.regs.PhysicalCount,
                        _PC := s'.regs._PC, ShouldAdvanceSS := s'.regs.ShouldAdvanceSS,
                        ShouldAdvanceIT := s'.regs.ShouldAdvanceIT, PSTATE := s'.regs.PSTATE,
                        PMULastThresholdValue := s'.regs.PMULastThresholdValue,
                        PMUEventAccumulator := s'.regs.PMUEventAccumulator,
                        VariantImplemented := s'.regs.VariantImplemented, FeatureImpl := s'.regs.FeatureImpl,
                        bank_BitVec_32 := s'.regs.bank_BitVec_32,
                        bank_Vector_BitVec_32_16 := s'.regs.bank_Vector_BitVec_32_16,
                        bank_Vector_BitVec_32_4 := s'.regs.bank_Vector_BitVec_32_4,
                        bank_Vector_BitVec_64_32 := s'.regs.bank_Vector_BitVec_64_32,
                        bank_BitVec_64 := s'.regs.bank_BitVec_64,
                        bank_Vector_BitVec_64_16 := s'.regs.bank_Vector_BitVec_64_16,
                        bank_Vector_BitVec_64_4 := s'.regs.bank_Vector_BitVec_64_4,
                        bank_Vector_BitVec_32_31 := s'.regs.bank_Vector_BitVec_32_31,
                        bank_Bool := s'.regs.bank_Bool.set ArmFull.Bank_Bool.InGuardedPage Bool.false,
                        bank_Int := s'.regs.bank_Int, bank_BitVec_1 := s'.regs.bank_BitVec_1,
                        bank_BitVec_56 := s'.regs.bank_BitVec_56, bank_BitVec_16 := s'.regs.bank_BitVec_16,
                        bank_BitVec_4 := s'.regs.bank_BitVec_4, bank_BitVec_128 := s'.regs.bank_BitVec_128,
                        bank_Vector_Bool_32 := s'.regs.bank_Vector_Bool_32,
                        bank_Vector_BitVec_64_64 := s'.regs.bank_Vector_BitVec_64_64,
                        bank_Option_InterruptID := s'.regs.bank_Option_InterruptID,
                        bank_BitVec_8 := s'.regs.bank_BitVec_8, bank_BitVec_2 := s'.regs.bank_BitVec_2,
                        bank_Vector_BitVec_64_7 := s'.regs.bank_Vector_BitVec_64_7,
                        bank_Signal := s'.regs.bank_Signal },
                    choiceState := s'.choiceState, choiceOcc := s'.choiceOcc, mem := s'.mem, tags := s'.tags,
                    cycleCount := s'.cycleCount, sailOutput := s'.sailOutput, events := s'.events })
                (fun a s' =>
                  cond a.not
                    (Bind.bind
                      (Bind.bind
                        (ArmFull.readReg
                          { get := fun r => r.PSTATE,
                            set := fun v r =>
                              { gpr := r.gpr, __emulator_termination_opcode := r.__emulator_termination_opcode,
                                PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                                SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                                SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max,
                                __BranchTaken := r.__BranchTaken, Branchtypetaken := r.Branchtypetaken,
                                __ThisInstrEnc := r.__ThisInstrEnc, __SPE_LFSR := r.__SPE_LFSR,
                                SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR,
                                FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P, _Z := r._Z,
                                BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext, RC := r.RC,
                                PhysicalCount := r.PhysicalCount, _PC := r._PC, ShouldAdvanceSS := r.ShouldAdvanceSS,
                                ShouldAdvanceIT := r.ShouldAdvanceIT, PSTATE := v,
                                PMULastThresholdValue := r.PMULastThresholdValue,
                                PMUEventAccumulator := r.PMUEventAccumulator,
                                VariantImplemented := r.VariantImplemented, FeatureImpl := r.FeatureImpl,
                                bank_BitVec_32 := r.bank_BitVec_32,
                                bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                                bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                                bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                                bank_BitVec_64 := r.bank_BitVec_64,
                                bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                                bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                                bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31, bank_Bool := r.bank_Bool,
                                bank_Int := r.bank_Int, bank_BitVec_1 := r.bank_BitVec_1,
                                bank_BitVec_56 := r.bank_BitVec_56, bank_BitVec_16 := r.bank_BitVec_16,
                                bank_BitVec_4 := r.bank_BitVec_4, bank_BitVec_128 := r.bank_BitVec_128,
                                bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                                bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                                bank_Option_InterruptID := r.bank_Option_InterruptID, bank_BitVec_8 := r.bank_BitVec_8,
                                bank_BitVec_2 := r.bank_BitVec_2, bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
                                bank_Signal := r.bank_Signal } })
                        fun w__9 =>
                        Bind.bind (ArmFull.readReg ArmFull.Register.BTypeNext) fun w__10 =>
                          ArmFull.writeReg
                            { get := fun r => r.PSTATE,
                              set := fun v r =>
                                { gpr := r.gpr, __emulator_termination_opcode := r.__emulator_termination_opcode,
                                  PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                                  SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                                  SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max,
                                  __BranchTaken := r.__BranchTaken, Branchtypetaken := r.Branchtypetaken,
                                  __ThisInstrEnc := r.__ThisInstrEnc, __SPE_LFSR := r.__SPE_LFSR,
                                  SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR,
                                  FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P, _Z := r._Z,
                                  BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext, RC := r.RC,
                                  PhysicalCount := r.PhysicalCount, _PC := r._PC, ShouldAdvanceSS := r.ShouldAdvanceSS,
                                  ShouldAdvanceIT := r.ShouldAdvanceIT, PSTATE := v,
                                  PMULastThresholdValue := r.PMULastThresholdValue,
                                  PMUEventAccumulator := r.PMUEventAccumulator,
                                  VariantImplemented := r.VariantImplemented, FeatureImpl := r.FeatureImpl,
                                  bank_BitVec_32 := r.bank_BitVec_32,
                                  bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                                  bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                                  bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                                  bank_BitVec_64 := r.bank_BitVec_64,
                                  bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                                  bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                                  bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31, bank_Bool := r.bank_Bool,
                                  bank_Int := r.bank_Int, bank_BitVec_1 := r.bank_BitVec_1,
                                  bank_BitVec_56 := r.bank_BitVec_56, bank_BitVec_16 := r.bank_BitVec_16,
                                  bank_BitVec_4 := r.bank_BitVec_4, bank_BitVec_128 := r.bank_BitVec_128,
                                  bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                                  bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                                  bank_Option_InterruptID := r.bank_Option_InterruptID,
                                  bank_BitVec_8 := r.bank_BitVec_8, bank_BitVec_2 := r.bank_BitVec_2,
                                  bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7, bank_Signal := r.bank_Signal } }
                            { N := w__9.N, Z := w__9.Z, C := w__9.C, V := w__9.V, D := w__9.D, A := w__9.A, I := w__9.I,
                              F := w__9.F, EXLOCK := w__9.EXLOCK, PAN := w__9.PAN, UAO := w__9.UAO, DIT := w__9.DIT,
                              TCO := w__9.TCO, PM := w__9.PM, PPEND := w__9.PPEND, BTYPE := w__10, ZA := w__9.ZA,
                              SM := w__9.SM, ALLINT := w__9.ALLINT, SS := w__9.SS, IL := w__9.IL, EL := w__9.EL,
                              nRW := w__9.nRW, SP := w__9.SP, Q := w__9.Q, GE := w__9.GE, SSBS := w__9.SSBS,
                              IT := w__9.IT, J := w__9.J, T := w__9.T, E := w__9.E, M := w__9.M })
                      fun __r =>
                      Bind.bind
                        (ArmFull.readReg
                          { get := fun r => r.__BranchTaken,
                            set := fun v r =>
                              { gpr := r.gpr, __emulator_termination_opcode := r.__emulator_termination_opcode,
                                PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                                SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                                SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max,
                                __BranchTaken := v, Branchtypetaken := r.Branchtypetaken,
                                __ThisInstrEnc := r.__ThisInstrEnc, __SPE_LFSR := r.__SPE_LFSR,
                                SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR,
                                FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P, _Z := r._Z,
                                BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext, RC := r.RC,
                                PhysicalCount := r.PhysicalCount, _PC := r._PC, ShouldAdvanceSS := r.ShouldAdvanceSS,
                                ShouldAdvanceIT := r.ShouldAdvanceIT, PSTATE := r.PSTATE,
                                PMULastThresholdValue := r.PMULastThresholdValue,
                                PMUEventAccumulator := r.PMUEventAccumulator,
                                VariantImplemented := r.VariantImplemented, FeatureImpl := r.FeatureImpl,
                                bank_BitVec_32 := r.bank_BitVec_32,
                                bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                                bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                                bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                                bank_BitVec_64 := r.bank_BitVec_64,
                                bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                                bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                                bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31, bank_Bool := r.bank_Bool,
                                bank_Int := r.bank_Int, bank_BitVec_1 := r.bank_BitVec_1,
                                bank_BitVec_56 := r.bank_BitVec_56, bank_BitVec_16 := r.bank_BitVec_16,
                                bank_BitVec_4 := r.bank_BitVec_4, bank_BitVec_128 := r.bank_BitVec_128,
                                bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                                bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                                bank_Option_InterruptID := r.bank_Option_InterruptID, bank_BitVec_8 := r.bank_BitVec_8,
                                bank_BitVec_2 := r.bank_BitVec_2, bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
                                bank_Signal := r.bank_Signal } })
                        fun w__11 =>
                        cond w__11.not
                          (Bind.bind
                            (Bind.bind (ArmFull.readReg ArmFull.Register._PC) fun w__12 =>
                              Bind.bind (ArmFull.Functions.ThisInstrLength Unit.unit) fun w__13 =>
                                ArmFull.writeReg ArmFull.Register._PC
                                  (Sail.BitVec.extractLsb
                                    (Sail.BitVec.addInt w__12 (ArmFull.Functions.fdiv_int w__13 8)) 63 0))
                            fun __r =>
                            Bind.bind
                              (ArmFull.readReg
                                { get := fun r => r.ShouldAdvanceIT,
                                  set := fun v r =>
                                    { gpr := r.gpr, __emulator_termination_opcode := r.__emulator_termination_opcode,
                                      PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                                      SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                                      SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max,
                                      __BranchTaken := r.__BranchTaken, Branchtypetaken := r.Branchtypetaken,
                                      __ThisInstrEnc := r.__ThisInstrEnc, __SPE_LFSR := r.__SPE_LFSR,
                                      SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR,
                                      FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P,
                                      _Z := r._Z, BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext,
                                      RC := r.RC, PhysicalCount := r.PhysicalCount, _PC := r._PC,
                                      ShouldAdvanceSS := r.ShouldAdvanceSS, ShouldAdvanceIT := v, PSTATE := r.PSTATE,
                                      PMULastThresholdValue := r.PMULastThresholdValue,
                                      PMUEventAccumulator := r.PMUEventAccumulator,
                                      VariantImplemented := r.VariantImplemented, FeatureImpl := r.FeatureImpl,
                                      bank_BitVec_32 := r.bank_BitVec_32,
                                      bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                                      bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                                      bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                                      bank_BitVec_64 := r.bank_BitVec_64,
                                      bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                                      bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                                      bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31, bank_Bool := r.bank_Bool,
                                      bank_Int := r.bank_Int, bank_BitVec_1 := r.bank_BitVec_1,
                                      bank_BitVec_56 := r.bank_BitVec_56, bank_BitVec_16 := r.bank_BitVec_16,
                                      bank_BitVec_4 := r.bank_BitVec_4, bank_BitVec_128 := r.bank_BitVec_128,
                                      bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                                      bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                                      bank_Option_InterruptID := r.bank_Option_InterruptID,
                                      bank_BitVec_8 := r.bank_BitVec_8, bank_BitVec_2 := r.bank_BitVec_2,
                                      bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
                                      bank_Signal := r.bank_Signal } })
                              fun w__14 =>
                              cond w__14
                                (Bind.bind (ArmFull.Functions.AArch32_ITAdvance Unit.unit) fun __r =>
                                  Bind.bind
                                    (ArmFull.readReg
                                      { get := fun r => r.ShouldAdvanceSS,
                                        set := fun v r =>
                                          { gpr := r.gpr,
                                            __emulator_termination_opcode := r.__emulator_termination_opcode,
                                            PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                                            SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                                            SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0,
                                            __mpam_vpmr_max := r.__mpam_vpmr_max, __BranchTaken := r.__BranchTaken,
                                            Branchtypetaken := r.Branchtypetaken, __ThisInstrEnc := r.__ThisInstrEnc,
                                            __SPE_LFSR := r.__SPE_LFSR, SPESampleOpType := r.SPESampleOpType,
                                            TSTATE := r.TSTATE, FPSR := r.FPSR, FPCR := r.FPCR, _ZT0 := r._ZT0,
                                            _ZA := r._ZA, _FFR := r._FFR, _P := r._P, _Z := r._Z,
                                            BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext, RC := r.RC,
                                            PhysicalCount := r.PhysicalCount, _PC := r._PC, ShouldAdvanceSS := v,
                                            ShouldAdvanceIT := r.ShouldAdvanceIT, PSTATE := r.PSTATE,
                                            PMULastThresholdValue := r.PMULastThresholdValue,
                                            PMUEventAccumulator := r.PMUEventAccumulator,
                                            VariantImplemented := r.VariantImplemented, FeatureImpl := r.FeatureImpl,
                                            bank_BitVec_32 := r.bank_BitVec_32,
                                            bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                                            bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                                            bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                                            bank_BitVec_64 := r.bank_BitVec_64,
                                            bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                                            bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                                            bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31,
                                            bank_Bool := r.bank_Bool, bank_Int := r.bank_Int,
                                            bank_BitVec_1 := r.bank_BitVec_1, bank_BitVec_56 := r.bank_BitVec_56,
                                            bank_BitVec_16 := r.bank_BitVec_16, bank_BitVec_4 := r.bank_BitVec_4,
                                            bank_BitVec_128 := r.bank_BitVec_128,
                                            bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                                            bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                                            bank_Option_InterruptID := r.bank_Option_InterruptID,
                                            bank_BitVec_8 := r.bank_BitVec_8, bank_BitVec_2 := r.bank_BitVec_2,
                                            bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
                                            bank_Signal := r.bank_Signal } })
                                    fun w__15 =>
                                    cond w__15 (ArmFull.Functions.SSAdvance Unit.unit) (EStateM.pure Unit.unit))
                                (Bind.bind
                                  (ArmFull.readReg
                                    { get := fun r => r.ShouldAdvanceSS,
                                      set := fun v r =>
                                        { gpr := r.gpr,
                                          __emulator_termination_opcode := r.__emulator_termination_opcode,
                                          PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                                          SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                                          SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max,
                                          __BranchTaken := r.__BranchTaken, Branchtypetaken := r.Branchtypetaken,
                                          __ThisInstrEnc := r.__ThisInstrEnc, __SPE_LFSR := r.__SPE_LFSR,
                                          SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR,
                                          FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P,
                                          _Z := r._Z, BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext,
                                          RC := r.RC, PhysicalCount := r.PhysicalCount, _PC := r._PC,
                                          ShouldAdvanceSS := v, ShouldAdvanceIT := r.ShouldAdvanceIT,
                                          PSTATE := r.PSTATE, PMULastThresholdValue := r.PMULastThresholdValue,
                                          PMUEventAccumulator := r.PMUEventAccumulator,
                                          VariantImplemented := r.VariantImplemented, FeatureImpl := r.FeatureImpl,
                                          bank_BitVec_32 := r.bank_BitVec_32,
                                          bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                                          bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                                          bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                                          bank_BitVec_64 := r.bank_BitVec_64,
                                          bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                                          bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                                          bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31,
                                          bank_Bool := r.bank_Bool, bank_Int := r.bank_Int,
                                          bank_BitVec_1 := r.bank_BitVec_1, bank_BitVec_56 := r.bank_BitVec_56,
                                          bank_BitVec_16 := r.bank_BitVec_16, bank_BitVec_4 := r.bank_BitVec_4,
                                          bank_BitVec_128 := r.bank_BitVec_128,
                                          bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                                          bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                                          bank_Option_InterruptID := r.bank_Option_InterruptID,
                                          bank_BitVec_8 := r.bank_BitVec_8, bank_BitVec_2 := r.bank_BitVec_2,
                                          bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
                                          bank_Signal := r.bank_Signal } })
                                  fun w__15 =>
                                  cond w__15 (ArmFull.Functions.SSAdvance Unit.unit) (EStateM.pure Unit.unit)))
                          (Bind.bind
                            (ArmFull.readReg
                              { get := fun r => r.ShouldAdvanceIT,
                                set := fun v r =>
                                  { gpr := r.gpr, __emulator_termination_opcode := r.__emulator_termination_opcode,
                                    PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                                    SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                                    SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max,
                                    __BranchTaken := r.__BranchTaken, Branchtypetaken := r.Branchtypetaken,
                                    __ThisInstrEnc := r.__ThisInstrEnc, __SPE_LFSR := r.__SPE_LFSR,
                                    SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR,
                                    FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P,
                                    _Z := r._Z, BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext,
                                    RC := r.RC, PhysicalCount := r.PhysicalCount, _PC := r._PC,
                                    ShouldAdvanceSS := r.ShouldAdvanceSS, ShouldAdvanceIT := v, PSTATE := r.PSTATE,
                                    PMULastThresholdValue := r.PMULastThresholdValue,
                                    PMUEventAccumulator := r.PMUEventAccumulator,
                                    VariantImplemented := r.VariantImplemented, FeatureImpl := r.FeatureImpl,
                                    bank_BitVec_32 := r.bank_BitVec_32,
                                    bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                                    bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                                    bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                                    bank_BitVec_64 := r.bank_BitVec_64,
                                    bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                                    bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                                    bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31, bank_Bool := r.bank_Bool,
                                    bank_Int := r.bank_Int, bank_BitVec_1 := r.bank_BitVec_1,
                                    bank_BitVec_56 := r.bank_BitVec_56, bank_BitVec_16 := r.bank_BitVec_16,
                                    bank_BitVec_4 := r.bank_BitVec_4, bank_BitVec_128 := r.bank_BitVec_128,
                                    bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                                    bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                                    bank_Option_InterruptID := r.bank_Option_InterruptID,
                                    bank_BitVec_8 := r.bank_BitVec_8, bank_BitVec_2 := r.bank_BitVec_2,
                                    bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
                                    bank_Signal := r.bank_Signal } })
                            fun w__14 =>
                            cond w__14
                              (Bind.bind (ArmFull.Functions.AArch32_ITAdvance Unit.unit) fun __r =>
                                Bind.bind
                                  (ArmFull.readReg
                                    { get := fun r => r.ShouldAdvanceSS,
                                      set := fun v r =>
                                        { gpr := r.gpr,
                                          __emulator_termination_opcode := r.__emulator_termination_opcode,
                                          PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                                          SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                                          SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max,
                                          __BranchTaken := r.__BranchTaken, Branchtypetaken := r.Branchtypetaken,
                                          __ThisInstrEnc := r.__ThisInstrEnc, __SPE_LFSR := r.__SPE_LFSR,
                                          SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR,
                                          FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P,
                                          _Z := r._Z, BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext,
                                          RC := r.RC, PhysicalCount := r.PhysicalCount, _PC := r._PC,
                                          ShouldAdvanceSS := v, ShouldAdvanceIT := r.ShouldAdvanceIT,
                                          PSTATE := r.PSTATE, PMULastThresholdValue := r.PMULastThresholdValue,
                                          PMUEventAccumulator := r.PMUEventAccumulator,
                                          VariantImplemented := r.VariantImplemented, FeatureImpl := r.FeatureImpl,
                                          bank_BitVec_32 := r.bank_BitVec_32,
                                          bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                                          bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                                          bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                                          bank_BitVec_64 := r.bank_BitVec_64,
                                          bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                                          bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                                          bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31,
                                          bank_Bool := r.bank_Bool, bank_Int := r.bank_Int,
                                          bank_BitVec_1 := r.bank_BitVec_1, bank_BitVec_56 := r.bank_BitVec_56,
                                          bank_BitVec_16 := r.bank_BitVec_16, bank_BitVec_4 := r.bank_BitVec_4,
                                          bank_BitVec_128 := r.bank_BitVec_128,
                                          bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                                          bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                                          bank_Option_InterruptID := r.bank_Option_InterruptID,
                                          bank_BitVec_8 := r.bank_BitVec_8, bank_BitVec_2 := r.bank_BitVec_2,
                                          bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
                                          bank_Signal := r.bank_Signal } })
                                  fun w__15 =>
                                  cond w__15 (ArmFull.Functions.SSAdvance Unit.unit) (EStateM.pure Unit.unit))
                              (Bind.bind
                                (ArmFull.readReg
                                  { get := fun r => r.ShouldAdvanceSS,
                                    set := fun v r =>
                                      { gpr := r.gpr, __emulator_termination_opcode := r.__emulator_termination_opcode,
                                        PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                                        SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                                        SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max,
                                        __BranchTaken := r.__BranchTaken, Branchtypetaken := r.Branchtypetaken,
                                        __ThisInstrEnc := r.__ThisInstrEnc, __SPE_LFSR := r.__SPE_LFSR,
                                        SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR,
                                        FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P,
                                        _Z := r._Z, BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext,
                                        RC := r.RC, PhysicalCount := r.PhysicalCount, _PC := r._PC,
                                        ShouldAdvanceSS := v, ShouldAdvanceIT := r.ShouldAdvanceIT, PSTATE := r.PSTATE,
                                        PMULastThresholdValue := r.PMULastThresholdValue,
                                        PMUEventAccumulator := r.PMUEventAccumulator,
                                        VariantImplemented := r.VariantImplemented, FeatureImpl := r.FeatureImpl,
                                        bank_BitVec_32 := r.bank_BitVec_32,
                                        bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                                        bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                                        bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                                        bank_BitVec_64 := r.bank_BitVec_64,
                                        bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                                        bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                                        bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31,
                                        bank_Bool := r.bank_Bool, bank_Int := r.bank_Int,
                                        bank_BitVec_1 := r.bank_BitVec_1, bank_BitVec_56 := r.bank_BitVec_56,
                                        bank_BitVec_16 := r.bank_BitVec_16, bank_BitVec_4 := r.bank_BitVec_4,
                                        bank_BitVec_128 := r.bank_BitVec_128,
                                        bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                                        bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                                        bank_Option_InterruptID := r.bank_Option_InterruptID,
                                        bank_BitVec_8 := r.bank_BitVec_8, bank_BitVec_2 := r.bank_BitVec_2,
                                        bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
                                        bank_Signal := r.bank_Signal } })
                                fun w__15 =>
                                cond w__15 (ArmFull.Functions.SSAdvance Unit.unit) (EStateM.pure Unit.unit))))
                    (Bind.bind
                      (ArmFull.readReg
                        { get := fun r => r.__BranchTaken,
                          set := fun v r =>
                            { gpr := r.gpr, __emulator_termination_opcode := r.__emulator_termination_opcode,
                              PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                              SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                              SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max,
                              __BranchTaken := v, Branchtypetaken := r.Branchtypetaken,
                              __ThisInstrEnc := r.__ThisInstrEnc, __SPE_LFSR := r.__SPE_LFSR,
                              SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR, FPCR := r.FPCR,
                              _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P, _Z := r._Z,
                              BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext, RC := r.RC,
                              PhysicalCount := r.PhysicalCount, _PC := r._PC, ShouldAdvanceSS := r.ShouldAdvanceSS,
                              ShouldAdvanceIT := r.ShouldAdvanceIT, PSTATE := r.PSTATE,
                              PMULastThresholdValue := r.PMULastThresholdValue,
                              PMUEventAccumulator := r.PMUEventAccumulator, VariantImplemented := r.VariantImplemented,
                              FeatureImpl := r.FeatureImpl, bank_BitVec_32 := r.bank_BitVec_32,
                              bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                              bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                              bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                              bank_BitVec_64 := r.bank_BitVec_64,
                              bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                              bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                              bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31, bank_Bool := r.bank_Bool,
                              bank_Int := r.bank_Int, bank_BitVec_1 := r.bank_BitVec_1,
                              bank_BitVec_56 := r.bank_BitVec_56, bank_BitVec_16 := r.bank_BitVec_16,
                              bank_BitVec_4 := r.bank_BitVec_4, bank_BitVec_128 := r.bank_BitVec_128,
                              bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                              bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                              bank_Option_InterruptID := r.bank_Option_InterruptID, bank_BitVec_8 := r.bank_BitVec_8,
                              bank_BitVec_2 := r.bank_BitVec_2, bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
                              bank_Signal := r.bank_Signal } })
                      fun w__11 =>
                      cond w__11.not
                        (Bind.bind
                          (Bind.bind (ArmFull.readReg ArmFull.Register._PC) fun w__12 =>
                            Bind.bind (ArmFull.Functions.ThisInstrLength Unit.unit) fun w__13 =>
                              ArmFull.writeReg ArmFull.Register._PC
                                (Sail.BitVec.extractLsb (Sail.BitVec.addInt w__12 (ArmFull.Functions.fdiv_int w__13 8))
                                  63 0))
                          fun __r =>
                          Bind.bind
                            (ArmFull.readReg
                              { get := fun r => r.ShouldAdvanceIT,
                                set := fun v r =>
                                  { gpr := r.gpr, __emulator_termination_opcode := r.__emulator_termination_opcode,
                                    PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                                    SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                                    SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max,
                                    __BranchTaken := r.__BranchTaken, Branchtypetaken := r.Branchtypetaken,
                                    __ThisInstrEnc := r.__ThisInstrEnc, __SPE_LFSR := r.__SPE_LFSR,
                                    SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR,
                                    FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P,
                                    _Z := r._Z, BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext,
                                    RC := r.RC, PhysicalCount := r.PhysicalCount, _PC := r._PC,
                                    ShouldAdvanceSS := r.ShouldAdvanceSS, ShouldAdvanceIT := v, PSTATE := r.PSTATE,
                                    PMULastThresholdValue := r.PMULastThresholdValue,
                                    PMUEventAccumulator := r.PMUEventAccumulator,
                                    VariantImplemented := r.VariantImplemented, FeatureImpl := r.FeatureImpl,
                                    bank_BitVec_32 := r.bank_BitVec_32,
                                    bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                                    bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                                    bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                                    bank_BitVec_64 := r.bank_BitVec_64,
                                    bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                                    bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                                    bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31, bank_Bool := r.bank_Bool,
                                    bank_Int := r.bank_Int, bank_BitVec_1 := r.bank_BitVec_1,
                                    bank_BitVec_56 := r.bank_BitVec_56, bank_BitVec_16 := r.bank_BitVec_16,
                                    bank_BitVec_4 := r.bank_BitVec_4, bank_BitVec_128 := r.bank_BitVec_128,
                                    bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                                    bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                                    bank_Option_InterruptID := r.bank_Option_InterruptID,
                                    bank_BitVec_8 := r.bank_BitVec_8, bank_BitVec_2 := r.bank_BitVec_2,
                                    bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
                                    bank_Signal := r.bank_Signal } })
                            fun w__14 =>
                            cond w__14
                              (Bind.bind (ArmFull.Functions.AArch32_ITAdvance Unit.unit) fun __r =>
                                Bind.bind
                                  (ArmFull.readReg
                                    { get := fun r => r.ShouldAdvanceSS,
                                      set := fun v r =>
                                        { gpr := r.gpr,
                                          __emulator_termination_opcode := r.__emulator_termination_opcode,
                                          PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                                          SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                                          SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max,
                                          __BranchTaken := r.__BranchTaken, Branchtypetaken := r.Branchtypetaken,
                                          __ThisInstrEnc := r.__ThisInstrEnc, __SPE_LFSR := r.__SPE_LFSR,
                                          SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR,
                                          FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P,
                                          _Z := r._Z, BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext,
                                          RC := r.RC, PhysicalCount := r.PhysicalCount, _PC := r._PC,
                                          ShouldAdvanceSS := v, ShouldAdvanceIT := r.ShouldAdvanceIT,
                                          PSTATE := r.PSTATE, PMULastThresholdValue := r.PMULastThresholdValue,
                                          PMUEventAccumulator := r.PMUEventAccumulator,
                                          VariantImplemented := r.VariantImplemented, FeatureImpl := r.FeatureImpl,
                                          bank_BitVec_32 := r.bank_BitVec_32,
                                          bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                                          bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                                          bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                                          bank_BitVec_64 := r.bank_BitVec_64,
                                          bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                                          bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                                          bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31,
                                          bank_Bool := r.bank_Bool, bank_Int := r.bank_Int,
                                          bank_BitVec_1 := r.bank_BitVec_1, bank_BitVec_56 := r.bank_BitVec_56,
                                          bank_BitVec_16 := r.bank_BitVec_16, bank_BitVec_4 := r.bank_BitVec_4,
                                          bank_BitVec_128 := r.bank_BitVec_128,
                                          bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                                          bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                                          bank_Option_InterruptID := r.bank_Option_InterruptID,
                                          bank_BitVec_8 := r.bank_BitVec_8, bank_BitVec_2 := r.bank_BitVec_2,
                                          bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
                                          bank_Signal := r.bank_Signal } })
                                  fun w__15 =>
                                  cond w__15 (ArmFull.Functions.SSAdvance Unit.unit) (EStateM.pure Unit.unit))
                              (Bind.bind
                                (ArmFull.readReg
                                  { get := fun r => r.ShouldAdvanceSS,
                                    set := fun v r =>
                                      { gpr := r.gpr, __emulator_termination_opcode := r.__emulator_termination_opcode,
                                        PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                                        SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                                        SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max,
                                        __BranchTaken := r.__BranchTaken, Branchtypetaken := r.Branchtypetaken,
                                        __ThisInstrEnc := r.__ThisInstrEnc, __SPE_LFSR := r.__SPE_LFSR,
                                        SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR,
                                        FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P,
                                        _Z := r._Z, BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext,
                                        RC := r.RC, PhysicalCount := r.PhysicalCount, _PC := r._PC,
                                        ShouldAdvanceSS := v, ShouldAdvanceIT := r.ShouldAdvanceIT, PSTATE := r.PSTATE,
                                        PMULastThresholdValue := r.PMULastThresholdValue,
                                        PMUEventAccumulator := r.PMUEventAccumulator,
                                        VariantImplemented := r.VariantImplemented, FeatureImpl := r.FeatureImpl,
                                        bank_BitVec_32 := r.bank_BitVec_32,
                                        bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                                        bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                                        bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                                        bank_BitVec_64 := r.bank_BitVec_64,
                                        bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                                        bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                                        bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31,
                                        bank_Bool := r.bank_Bool, bank_Int := r.bank_Int,
                                        bank_BitVec_1 := r.bank_BitVec_1, bank_BitVec_56 := r.bank_BitVec_56,
                                        bank_BitVec_16 := r.bank_BitVec_16, bank_BitVec_4 := r.bank_BitVec_4,
                                        bank_BitVec_128 := r.bank_BitVec_128,
                                        bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                                        bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                                        bank_Option_InterruptID := r.bank_Option_InterruptID,
                                        bank_BitVec_8 := r.bank_BitVec_8, bank_BitVec_2 := r.bank_BitVec_2,
                                        bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
                                        bank_Signal := r.bank_Signal } })
                                fun w__15 =>
                                cond w__15 (ArmFull.Functions.SSAdvance Unit.unit) (EStateM.pure Unit.unit)))
                        (Bind.bind
                          (ArmFull.readReg
                            { get := fun r => r.ShouldAdvanceIT,
                              set := fun v r =>
                                { gpr := r.gpr, __emulator_termination_opcode := r.__emulator_termination_opcode,
                                  PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                                  SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                                  SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max,
                                  __BranchTaken := r.__BranchTaken, Branchtypetaken := r.Branchtypetaken,
                                  __ThisInstrEnc := r.__ThisInstrEnc, __SPE_LFSR := r.__SPE_LFSR,
                                  SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR,
                                  FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P, _Z := r._Z,
                                  BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext, RC := r.RC,
                                  PhysicalCount := r.PhysicalCount, _PC := r._PC, ShouldAdvanceSS := r.ShouldAdvanceSS,
                                  ShouldAdvanceIT := v, PSTATE := r.PSTATE,
                                  PMULastThresholdValue := r.PMULastThresholdValue,
                                  PMUEventAccumulator := r.PMUEventAccumulator,
                                  VariantImplemented := r.VariantImplemented, FeatureImpl := r.FeatureImpl,
                                  bank_BitVec_32 := r.bank_BitVec_32,
                                  bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                                  bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                                  bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                                  bank_BitVec_64 := r.bank_BitVec_64,
                                  bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                                  bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                                  bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31, bank_Bool := r.bank_Bool,
                                  bank_Int := r.bank_Int, bank_BitVec_1 := r.bank_BitVec_1,
                                  bank_BitVec_56 := r.bank_BitVec_56, bank_BitVec_16 := r.bank_BitVec_16,
                                  bank_BitVec_4 := r.bank_BitVec_4, bank_BitVec_128 := r.bank_BitVec_128,
                                  bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                                  bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                                  bank_Option_InterruptID := r.bank_Option_InterruptID,
                                  bank_BitVec_8 := r.bank_BitVec_8, bank_BitVec_2 := r.bank_BitVec_2,
                                  bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
                                  bank_Signal := r.bank_Signal } })
                          fun w__14 =>
                          cond w__14
                            (Bind.bind (ArmFull.Functions.AArch32_ITAdvance Unit.unit) fun __r =>
                              Bind.bind
                                (ArmFull.readReg
                                  { get := fun r => r.ShouldAdvanceSS,
                                    set := fun v r =>
                                      { gpr := r.gpr, __emulator_termination_opcode := r.__emulator_termination_opcode,
                                        PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                                        SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                                        SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max,
                                        __BranchTaken := r.__BranchTaken, Branchtypetaken := r.Branchtypetaken,
                                        __ThisInstrEnc := r.__ThisInstrEnc, __SPE_LFSR := r.__SPE_LFSR,
                                        SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR,
                                        FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P,
                                        _Z := r._Z, BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext,
                                        RC := r.RC, PhysicalCount := r.PhysicalCount, _PC := r._PC,
                                        ShouldAdvanceSS := v, ShouldAdvanceIT := r.ShouldAdvanceIT, PSTATE := r.PSTATE,
                                        PMULastThresholdValue := r.PMULastThresholdValue,
                                        PMUEventAccumulator := r.PMUEventAccumulator,
                                        VariantImplemented := r.VariantImplemented, FeatureImpl := r.FeatureImpl,
                                        bank_BitVec_32 := r.bank_BitVec_32,
                                        bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                                        bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                                        bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                                        bank_BitVec_64 := r.bank_BitVec_64,
                                        bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                                        bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                                        bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31,
                                        bank_Bool := r.bank_Bool, bank_Int := r.bank_Int,
                                        bank_BitVec_1 := r.bank_BitVec_1, bank_BitVec_56 := r.bank_BitVec_56,
                                        bank_BitVec_16 := r.bank_BitVec_16, bank_BitVec_4 := r.bank_BitVec_4,
                                        bank_BitVec_128 := r.bank_BitVec_128,
                                        bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                                        bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                                        bank_Option_InterruptID := r.bank_Option_InterruptID,
                                        bank_BitVec_8 := r.bank_BitVec_8, bank_BitVec_2 := r.bank_BitVec_2,
                                        bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
                                        bank_Signal := r.bank_Signal } })
                                fun w__15 =>
                                cond w__15 (ArmFull.Functions.SSAdvance Unit.unit) (EStateM.pure Unit.unit))
                            (Bind.bind
                              (ArmFull.readReg
                                { get := fun r => r.ShouldAdvanceSS,
                                  set := fun v r =>
                                    { gpr := r.gpr, __emulator_termination_opcode := r.__emulator_termination_opcode,
                                      PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                                      SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2,
                                      SP_EL1 := r.SP_EL1, SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max,
                                      __BranchTaken := r.__BranchTaken, Branchtypetaken := r.Branchtypetaken,
                                      __ThisInstrEnc := r.__ThisInstrEnc, __SPE_LFSR := r.__SPE_LFSR,
                                      SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR,
                                      FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P,
                                      _Z := r._Z, BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext,
                                      RC := r.RC, PhysicalCount := r.PhysicalCount, _PC := r._PC, ShouldAdvanceSS := v,
                                      ShouldAdvanceIT := r.ShouldAdvanceIT, PSTATE := r.PSTATE,
                                      PMULastThresholdValue := r.PMULastThresholdValue,
                                      PMUEventAccumulator := r.PMUEventAccumulator,
                                      VariantImplemented := r.VariantImplemented, FeatureImpl := r.FeatureImpl,
                                      bank_BitVec_32 := r.bank_BitVec_32,
                                      bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                                      bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                                      bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32,
                                      bank_BitVec_64 := r.bank_BitVec_64,
                                      bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                                      bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                                      bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31, bank_Bool := r.bank_Bool,
                                      bank_Int := r.bank_Int, bank_BitVec_1 := r.bank_BitVec_1,
                                      bank_BitVec_56 := r.bank_BitVec_56, bank_BitVec_16 := r.bank_BitVec_16,
                                      bank_BitVec_4 := r.bank_BitVec_4, bank_BitVec_128 := r.bank_BitVec_128,
                                      bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
                                      bank_Vector_BitVec_64_64 := r.bank_Vector_BitVec_64_64,
                                      bank_Option_InterruptID := r.bank_Option_InterruptID,
                                      bank_BitVec_8 := r.bank_BitVec_8, bank_BitVec_2 := r.bank_BitVec_2,
                                      bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
                                      bank_Signal := r.bank_Signal } })
                              fun w__15 =>
                              cond w__15 (ArmFull.Functions.SSAdvance Unit.unit) (EStateM.pure Unit.unit))))
                    s')
                fun e s' => EStateM.Result.error e s')
            fun e s' => EStateM.Result.error e s')
        fun e s' => EStateM.Result.error e s')
      (fun a s' => EStateM.Result.ok a s')
      (fun u s' =>
        ArmFull.Functions.__TopLevel.match_1 (fun the_exception => ArmFull.SailM Unit) u
          (fun iesb_req =>
            EStateM.bind (ArmFull.Functions.UsingAArch32 Unit.unit) fun w__2 =>
              cond w__2 (ArmFull.Functions.AArch32_TakePhysicalSErrorException iesb_req)
                (ArmFull.Functions.AArch64_TakePhysicalSErrorException iesb_req))
          (fun x => EStateM.pure Unit.unit) (fun e => ArmFull.sailThrow e) s')
      fun e s' => EStateM.Result.error e s')
    (fun a s => ArmFull.Functions.__CycleEnd Unit.unit s) fun e s' => EStateM.Result.error e s'

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.metadata_boundary"
  (← IO.getStderr).flush

/- Primitive CURRENT-state fields read by metadata/SPE-pre/Halted. No fetch,
future execution/frame/Q, memory identity or BTYPE/BTN condition is a field. -/
structure MetadataGuard (s : NativeState) : Prop where
  f4 : s.regs.FeatureImpl[4]! = true
  rme : s.regs.FeatureImpl[232]! = false
  el : s.regs.PSTATE.EL = 0#2
  nrw : s.regs.PSTATE.nRW = 0#1
  e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  tge : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  scrns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1
  pmbe : _get_PMBLIMITR_EL1_Type_E (s.regs.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1
  status : _get_EDSCR_Type_STATUS (s.regs.bank_BitVec_32 ._EDSCR) = 0b000010#6
  see : s.regs.bank_Int .SEE = -1

/- Once-generic disjoint-bit identity for the ACTUAL EDSCR_read overlay. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmBridge.CruxGenGuarded.status_mdccsr"
  (← IO.getStderr).flush

theorem status_mdccsr (e : BitVec 32) (v : BitVec 2) :
    _get_EDSCR_Type_STATUS (Sail.BitVec.updateSubrange e 30 29 v) =
      _get_EDSCR_Type_STATUS e := by
  unfold _get_EDSCR_Type_STATUS
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h : i < 6 := by simpa using hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;>
    subst h <;> simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
      Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb]

run_cmd do
  IO.eprintln "CURRENT_DECL ArmBridge.CruxGenGuarded.halted_status"
  (← IO.getStderr).flush

theorem halted_status (s : NativeState)
    (status : _get_EDSCR_Type_STATUS (s.regs.bank_BitVec_32 ._EDSCR) = 0b000010#6) :
    (Halted () : SailM Bool) s = .ok false s := by
  unfold Halted EDSCR_read
  simp only [↓bind_app, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply,
    pure, EStateM.pure]
  simp only [_EDSCR, MDCCSR_EL0, Regs.ref_BitVec_32, Regs.ref_BitVec_64,
    status_mdccsr, status]
  simp [Halted, EDSCR_read, bind_app, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply,
    pure, EStateM.pure, _EDSCR, MDCCSR_EL0, Regs.ref_BitVec_32,
    Regs.ref_BitVec_64, status_mdccsr, status]

def DispatchAt (real : Type) [Sail.SailReal real] (w : BitVec 32)
    (A : SailM Unit) (K : Int) : Prop :=
  ∀ (pc : Int) (t : NativeState), (t.regs.bank_Int .SEE <b K) = true →
    (__DecodeA64 (real := real) pc w : SailM Unit) t = (do writeReg SEE K; A) t

/- Correct one-way scalar adapter. An actually provided all-state scalar law
implies the current-state law; BTI/HINT is NOT asserted to have that old law. -/
theorem dispatch_state_of_global (real : Type) [Sail.SailReal real]
    (w : BitVec 32) (A : SailM Unit) (K : Int)
    (law : ∀ pc, (__DecodeA64 (real := real) pc w : SailM Unit) = (do
      let c ← (do let x ← readReg SEE; pure (x <b K))
      if c = true then (do writeReg SEE K; A) else sailThrow (exception.Error_Undefined ()))) :
    DispatchAt real w A K := by
  intro pc t see
  rw [law]
  have read : ((do let x ← readReg SEE; pure (x <b K)) : SailM Bool) t =
      .ok (t.regs.bank_Int .SEE <b K) t := by rfl
  rw [bind_app, read]
  dsimp only []
  rw [if_pos see]

/- SAME compiler-extracted canonical states, now with actual-state dispatch.
SEE=-1 is an actual current guard; the spec hook producer below derives its
preservation. No unused legacy FetchSpec or StepPins0 is assumed here. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmBridge.CruxGenGuarded.metadata_boundary_at"
  (← IO.getStderr).flush

theorem metadata_boundary_at (real : Type) [Sail.SailReal real]
    (s : NativeState) (w : BitVec 32) (A : SailM Unit) (enc0 : __InstrEnc)
    (afterSpec : NativeState) (g : MetadataGuard afterSpec)
    (K : Int) (hK : ((-1 : Int) <b K) = true)
    (hdisp : DispatchAt real w A K) :
    afterSpecPmu real s w enc0 afterSpec =
      nativeAtAction real s w A enc0 (actionState w afterSpec K) := by
  have hF4 := g.f4
  have hRME := g.rme
  have hEL := g.el
  have hnRW := g.nrw
  have hE2H := g.e2h
  have hTGE := g.tge
  have hSCRNS := g.scrns
  have hPMBE := g.pmbe
  have hST := g.status
  have hRME' : afterSpec.regs.FeatureImpl[232] = false := by simpa using hRME
  have hF4' : afterSpec.regs.FeatureImpl[4] = true := by simpa using hF4
  have hST' : Sail.BitVec.extractLsb (afterSpec.regs.bank_BitVec_32 ._EDSCR) 5 0 = 2#6 := by
    simpa [_get_EDSCR_Type_STATUS] using hST
  unfold ArmBridge.CruxGenGuarded.afterSpecPmu
  try simp only [↓bind_app, Sail.ConcurrencyInterfaceV1.PreSail.writeReg_apply, defcond_a64,
    ArmBridge.BKmin.setdet, ArmBridge.BK.setdet_native]
  rw [spePre_frame (real := real)]
  rotate_left
  all_goals first
    | (simp (disch := first | rfl | assumption | decide) [Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, fetchRegs, clrGP, preFetchRegs, hF4, hRME, hF4', hRME', hEL,
        hnRW, hE2H, hTGE, hSCRNS, hPMBE]; done)
    | skip
  try simp only [↓bind_app]
  unfold __DecodeExecute
  rw [tc_apply]
  unfold __TryDecodeExecute ExecuteA64
  try simp only [ArmBridge.Awc.ite_cond]
  try simp only [↓bind_app, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply]
  rw [halted_status]
  all_goals first
    | exact g.status
    | (simpa (disch := decide) only [__currentCond, __ThisInstr, __ThisInstrEnc,
        __ExclusiveMonitorSet, __BranchTaken, Regs.ref_BitVec_4,
        Regs.ref_BitVec_32, Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne,
        Sail.ConcurrencyInterfaceV1.RegMap.set_same] using g.status)
    | skip
  try simp (disch := decide) only [__currentCond, __ThisInstr, __ThisInstrEnc, __ExclusiveMonitorSet, __BranchTaken,
    Regs.ref_BitVec_32, Regs.ref_BitVec_4, Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne,
    Sail.ConcurrencyInterfaceV1.RegMap.set_same, fetchRegs, clrGP, preFetchRegs, Register.BTypeCompatible, Register.__InstructionStep, Register.BTypeCompatible,
    status_pipeadv, _EDSCR, MDCCSR_EL0, Regs.ref_BitVec_64, status_mdccsr, g.status, hST']
  try simp (config := {decide := true}) only [BitVec.reduceBEq, BitVec.reduceEq, decide_false, decide_true, Bool.not_false,
    Bool.not_true, Bool.true_and, Bool.false_and, Bool.and_false, Bool.cond_false, Bool.cond_true]
  try simp only [↓bind_app, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply]
  rw [hdisp]
  all_goals first
    | (simpa (disch := decide) only [SEE, Regs.ref_Int, __currentCond, __ThisInstr,
        __ThisInstrEnc, __ExclusiveMonitorSet, __BranchTaken, Regs.ref_BitVec_4,
        Regs.ref_BitVec_32, Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne,
        Sail.ConcurrencyInterfaceV1.RegMap.set_same, g.see] using hK)
    | skip
  try simp only [↓bind_app, Sail.ConcurrencyInterfaceV1.PreSail.writeReg_apply]
  unfold nativeAtAction actionState
  rfl


run_cmd do
  IO.eprintln "CURRENT_DECL ArmBridge.CruxGenGuarded.MetadataGuard.after_E20"
  (← IO.getStderr).flush

theorem MetadataGuard.after_E20 {s t : NativeState} (g : MetadataGuard s)
    (frame : E20Frame s.regs t.regs) : MetadataGuard t := by
  have p := PMUFrame.of_E20 frame
  constructor
  · simpa only [p.feat] using g.f4
  · simpa only [p.feat] using g.rme
  · simpa only [p.pstate] using g.el
  · simpa only [p.pstate] using g.nrw
  · simpa only [p.hcr] using g.e2h
  · simpa only [p.hcr] using g.tge
  · simpa only [p.scr] using g.scrns
  · simpa only [p.pmb] using g.pmbe
  · simpa only [p.edscr] using g.status
  · simpa only [p.see] using g.see

#print axioms dispatch_state_of_global
#print axioms status_mdccsr
#print axioms halted_status
#print axioms metadata_boundary_at
#print axioms MetadataGuard.after_E20

/- Exact old metadata-stage signature is retained ONLY as a scalar adapter.
The shared implementation above carries neither FetchSpec nor BTYPE/BTN0. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmBridge.CruxGenGuarded.metadata_boundary"
  (← IO.getStderr).flush

theorem metadata_boundary (real : Type) [Sail.SailReal real] (s : NativeState)
    (hF4 : s.regs.FeatureImpl[4]! = true) (hRME : s.regs.FeatureImpl[232]! = false)
    (hSPE : s.regs.bank_Bool .SPESampleInFlight = false) (hEL : s.regs.PSTATE.EL = 0#2)
    (hnRW : s.regs.PSTATE.nRW = 0#1)
    (hEDECR : _get_EDECR_Type_RCE (s.regs.bank_BitVec_32 .EDECR) = 0#1)
    (hCTI : _get_CTIDEVCTL_Type_RCE (s.regs.bank_BitVec_32 .CTIDEVCTL) = 0#1)
    (hST : _get_EDSCR_Type_STATUS (s.regs.bank_BitVec_32 ._EDSCR) = 0b000010#6)
    (hEDESR : s.regs.bank_BitVec_32 .EDESR = 0#32)
    (hBT : s.regs.Branchtypetaken ≠ BranchType.BranchType_RESET)
    (w : BitVec 32) (hFS : FetchSpec s w)
    (hEmu : s.regs.__emulator_termination_opcode = none)
    (hE2H : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
    (hTGE : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
    (hSCRNS : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
    (hPMBE : _get_PMBLIMITR_EL1_Type_E (s.regs.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1)
    (hMDSS : _get_MDSCR_EL1_Type_SS (s.regs.bank_BitVec_64 .MDSCR_EL1) = 0#1)
    (hPMBS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (hDA : s.regs.PSTATE.A = 0#1) (hDI : s.regs.PSTATE.I = 0#1) (hDF : s.regs.PSTATE.F = 0#1)
    (hIL : s.regs.PSTATE.IL = 0#1) (hPSS : s.regs.PSTATE.SS = 0#1) (hBTY : s.regs.PSTATE.BTYPE = 0#2)
    (hBTN : s.regs.BTypeNext = 0#2)
(A : SailM Unit)
    (enc0 : __InstrEnc) (afterSpec : NativeState)
(hE20 : E20Frame (clrGP (fetchRegs (preFetchRegs s.regs))) afterSpec.regs)
    (K : Int) (hK : ((-1 : Int) <b K) = true)
    (hdisp : ∀ pc, (__DecodeA64 (real := real) pc w : SailM Unit) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b K))
      if c = true then (do writeReg Register.SEE K; A) else sailThrow (exception.Error_Undefined ())))
 :
    afterSpecPmu real s w enc0 afterSpec =
      nativeAtAction real s w A enc0 (actionState w afterSpec K) := by
  have p := PMUFrame.of_E20 hE20
  have g : MetadataGuard afterSpec := by
    constructor
    · simpa (disch := decide) only [p.feat, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hF4
    · simpa (disch := decide) only [p.feat, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hRME
    · simpa (disch := decide) only [p.pstate, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hEL
    · simpa (disch := decide) only [p.pstate, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hnRW
    · simpa (disch := decide) only [p.hcr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hE2H
    · simpa (disch := decide) only [p.hcr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hTGE
    · simpa (disch := decide) only [p.scr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hSCRNS
    · simpa (disch := decide) only [p.pmb, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hPMBE
    · simpa (disch := decide) only [p.edscr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hST
    · simp (disch := decide) only [p.see, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv]
  exact metadata_boundary_at real s w A enc0 afterSpec g K hK
    (dispatch_state_of_global real w A K hdisp)

#print axioms metadata_boundary

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.actionState_fields"
  (← IO.getStderr).flush

theorem actionState_fields (w : BitVec 32) (t : NativeState) (K : Int) :
    GuardFieldsEq t (actionState w t K) := by
  constructor
  all_goals first
    | rfl
    | (intro k hk; rfl)
    | (simp (disch := decide) only [actionState, RegMap.set_ne])

theorem actionState_quiet (w : BitVec 32) (t : NativeState) (K : Int)
    (ticks : Nat) (hq : HookQuiet ticks t) : HookQuiet ticks (actionState w t K) :=
  quiet_of_fields ticks t _ hq (actionState_fields w t K)

theorem actionState_mem (w : BitVec 32) (t : NativeState) (K : Int) :
    (actionState w t K).mem = t.mem := rfl

theorem actionState_events (w : BitVec 32) (t : NativeState) (K : Int) :
    (actionState w t K).events = t.events := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.actionState_cong"
  (← IO.getStderr).flush

theorem actionState_cong (w : BitVec 32) (s t : NativeState) (K : Int)
    (h : ArmBridge.CruxGen.CongIn s t) : ArmBridge.CruxGen.CongIn s (actionState w t K) := by
  have hsys : SysEq2 (actionState w t K).regs s.regs := by
    cases h.sys
    constructor <;> simp_all (config := {decide := true}) only [actionState, RegMap.set_ne]
  exact ⟨h.mem, h.gpr, h.sp, h.z, h.ps, hsys, h.spx1, h.spx2, h.spx3, h.el0⟩

#print axioms metadata_boundary
#print axioms actionState_fields
#print axioms actionState_quiet
#print axioms actionState_mem
#print axioms actionState_events
#print axioms actionState_cong
end ArmBridge.CruxGenGuarded
