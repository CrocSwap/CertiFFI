import Bridge.CruxCore
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! GENERATED from the private, source-exact common generator and
compiler-extracted actual expressions. The prefix chooses its own encoding
and retains actual interrupt/fetch choice bookkeeping. No global hook law,
oracle-independence premise or caller-supplied prefix result is used. -/

def encodingState : NativeState → NativeState :=
fun s =>
  {
    regs :=
      { gpr := s.regs.gpr, __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
        PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1, SPESampleCounter := s.regs.SPESampleCounter,
        SPERecordData := s.regs.SPERecordData, SP_EL3 := s.regs.SP_EL3, SP_EL2 := s.regs.SP_EL2,
        SP_EL1 := s.regs.SP_EL1, SP_EL0 := s.regs.SP_EL0, __mpam_vpmr_max := s.regs.__mpam_vpmr_max,
        __BranchTaken := s.regs.__BranchTaken, Branchtypetaken := s.regs.Branchtypetaken,
        __ThisInstrEnc := s.regs.__ThisInstrEnc, __SPE_LFSR := s.regs.__SPE_LFSR,
        SPESampleOpType := s.regs.SPESampleOpType, TSTATE := s.regs.TSTATE, FPSR := s.regs.FPSR, FPCR := s.regs.FPCR,
        _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA, _FFR := s.regs._FFR, _P := s.regs._P, _Z := s.regs._Z,
        BTypeCompatible := s.regs.BTypeCompatible, BTypeNext := s.regs.BTypeNext, RC := s.regs.RC,
        PhysicalCount := s.regs.PhysicalCount, _PC := s.regs._PC, ShouldAdvanceSS := s.regs.ShouldAdvanceSS,
        ShouldAdvanceIT := s.regs.ShouldAdvanceIT, PSTATE := s.regs.PSTATE,
        PMULastThresholdValue := s.regs.PMULastThresholdValue, PMUEventAccumulator := s.regs.PMUEventAccumulator,
        VariantImplemented := s.regs.VariantImplemented, FeatureImpl := s.regs.FeatureImpl,
        bank_BitVec_32 := s.regs.bank_BitVec_32, bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
        bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
        bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32, bank_BitVec_64 := s.regs.bank_BitVec_64,
        bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
        bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
        bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31, bank_Bool := s.regs.bank_Bool,
        bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1), bank_BitVec_1 := s.regs.bank_BitVec_1,
        bank_BitVec_56 := s.regs.bank_BitVec_56, bank_BitVec_16 := s.regs.bank_BitVec_16,
        bank_BitVec_4 := s.regs.bank_BitVec_4, bank_BitVec_128 := s.regs.bank_BitVec_128,
        bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32, bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
        bank_Option_InterruptID := s.regs.bank_Option_InterruptID, bank_BitVec_8 := s.regs.bank_BitVec_8,
        bank_BitVec_2 := s.regs.bank_BitVec_2, bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
        bank_Signal := s.regs.bank_Signal },
    choiceState :=
      ArmBridge.CruxCore.resCS
        {
          regs :=
            { gpr := s.regs.gpr, __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
              PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1, SPESampleCounter := s.regs.SPESampleCounter,
              SPERecordData := s.regs.SPERecordData, SP_EL3 := s.regs.SP_EL3, SP_EL2 := s.regs.SP_EL2,
              SP_EL1 := s.regs.SP_EL1, SP_EL0 := s.regs.SP_EL0, __mpam_vpmr_max := s.regs.__mpam_vpmr_max,
              __BranchTaken := s.regs.__BranchTaken, Branchtypetaken := s.regs.Branchtypetaken,
              __ThisInstrEnc := s.regs.__ThisInstrEnc, __SPE_LFSR := s.regs.__SPE_LFSR,
              SPESampleOpType := s.regs.SPESampleOpType, TSTATE := s.regs.TSTATE, FPSR := s.regs.FPSR,
              FPCR := s.regs.FPCR, _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA, _FFR := s.regs._FFR, _P := s.regs._P,
              _Z := s.regs._Z, BTypeCompatible := s.regs.BTypeCompatible, BTypeNext := s.regs.BTypeNext,
              RC := s.regs.RC, PhysicalCount := s.regs.PhysicalCount, _PC := s.regs._PC,
              ShouldAdvanceSS := s.regs.ShouldAdvanceSS, ShouldAdvanceIT := s.regs.ShouldAdvanceIT,
              PSTATE := s.regs.PSTATE, PMULastThresholdValue := s.regs.PMULastThresholdValue,
              PMUEventAccumulator := s.regs.PMUEventAccumulator, VariantImplemented := s.regs.VariantImplemented,
              FeatureImpl := s.regs.FeatureImpl, bank_BitVec_32 := s.regs.bank_BitVec_32,
              bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
              bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
              bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32, bank_BitVec_64 := s.regs.bank_BitVec_64,
              bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
              bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
              bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31, bank_Bool := s.regs.bank_Bool,
              bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1), bank_BitVec_1 := s.regs.bank_BitVec_1,
              bank_BitVec_56 := s.regs.bank_BitVec_56, bank_BitVec_16 := s.regs.bank_BitVec_16,
              bank_BitVec_4 := s.regs.bank_BitVec_4, bank_BitVec_128 := s.regs.bank_BitVec_128,
              bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32,
              bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
              bank_Option_InterruptID := s.regs.bank_Option_InterruptID, bank_BitVec_8 := s.regs.bank_BitVec_8,
              bank_BitVec_2 := s.regs.bank_BitVec_2, bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
              bank_Signal := s.regs.bank_Signal },
          choiceState := s.choiceState, choiceOcc := s.choiceOcc, mem := s.mem, tags := s.tags,
          cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events }
        (ArmFull.Functions.TakePendingInterrupts
          { take_SE := Bool.true, take_vSE := Bool.true, take_IRQ := Bool.true, take_vIRQ := Bool.true,
            take_FIQ := Bool.true, take_vFIQ := Bool.true,
            iesb_req :=
              Sail.ConcurrencyInterfaceV1.oracleChoiceSource.chooseAt Sail.Primitive.bool
                ((Sail.ConcurrencyInterfaceV1.ChoiceLabel.site 7640).child 6) s.choiceState }
          {
            regs :=
              { gpr := s.regs.gpr, __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
                PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1, SPESampleCounter := s.regs.SPESampleCounter,
                SPERecordData := s.regs.SPERecordData, SP_EL3 := s.regs.SP_EL3, SP_EL2 := s.regs.SP_EL2,
                SP_EL1 := s.regs.SP_EL1, SP_EL0 := s.regs.SP_EL0, __mpam_vpmr_max := s.regs.__mpam_vpmr_max,
                __BranchTaken := s.regs.__BranchTaken, Branchtypetaken := s.regs.Branchtypetaken,
                __ThisInstrEnc := s.regs.__ThisInstrEnc, __SPE_LFSR := s.regs.__SPE_LFSR,
                SPESampleOpType := s.regs.SPESampleOpType, TSTATE := s.regs.TSTATE, FPSR := s.regs.FPSR,
                FPCR := s.regs.FPCR, _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA, _FFR := s.regs._FFR, _P := s.regs._P,
                _Z := s.regs._Z, BTypeCompatible := s.regs.BTypeCompatible, BTypeNext := s.regs.BTypeNext,
                RC := s.regs.RC, PhysicalCount := s.regs.PhysicalCount, _PC := s.regs._PC,
                ShouldAdvanceSS := s.regs.ShouldAdvanceSS, ShouldAdvanceIT := s.regs.ShouldAdvanceIT,
                PSTATE := s.regs.PSTATE, PMULastThresholdValue := s.regs.PMULastThresholdValue,
                PMUEventAccumulator := s.regs.PMUEventAccumulator, VariantImplemented := s.regs.VariantImplemented,
                FeatureImpl := s.regs.FeatureImpl, bank_BitVec_32 := s.regs.bank_BitVec_32,
                bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
                bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
                bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32, bank_BitVec_64 := s.regs.bank_BitVec_64,
                bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
                bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
                bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31, bank_Bool := s.regs.bank_Bool,
                bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1), bank_BitVec_1 := s.regs.bank_BitVec_1,
                bank_BitVec_56 := s.regs.bank_BitVec_56, bank_BitVec_16 := s.regs.bank_BitVec_16,
                bank_BitVec_4 := s.regs.bank_BitVec_4, bank_BitVec_128 := s.regs.bank_BitVec_128,
                bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32,
                bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
                bank_Option_InterruptID := s.regs.bank_Option_InterruptID, bank_BitVec_8 := s.regs.bank_BitVec_8,
                bank_BitVec_2 := s.regs.bank_BitVec_2, bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
                bank_Signal := s.regs.bank_Signal },
            choiceState := s.choiceState, choiceOcc := s.choiceOcc, mem := s.mem, tags := s.tags,
            cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events }),
    choiceOcc :=
      ArmBridge.CruxCore.resCO
        {
          regs :=
            { gpr := s.regs.gpr, __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
              PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1, SPESampleCounter := s.regs.SPESampleCounter,
              SPERecordData := s.regs.SPERecordData, SP_EL3 := s.regs.SP_EL3, SP_EL2 := s.regs.SP_EL2,
              SP_EL1 := s.regs.SP_EL1, SP_EL0 := s.regs.SP_EL0, __mpam_vpmr_max := s.regs.__mpam_vpmr_max,
              __BranchTaken := s.regs.__BranchTaken, Branchtypetaken := s.regs.Branchtypetaken,
              __ThisInstrEnc := s.regs.__ThisInstrEnc, __SPE_LFSR := s.regs.__SPE_LFSR,
              SPESampleOpType := s.regs.SPESampleOpType, TSTATE := s.regs.TSTATE, FPSR := s.regs.FPSR,
              FPCR := s.regs.FPCR, _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA, _FFR := s.regs._FFR, _P := s.regs._P,
              _Z := s.regs._Z, BTypeCompatible := s.regs.BTypeCompatible, BTypeNext := s.regs.BTypeNext,
              RC := s.regs.RC, PhysicalCount := s.regs.PhysicalCount, _PC := s.regs._PC,
              ShouldAdvanceSS := s.regs.ShouldAdvanceSS, ShouldAdvanceIT := s.regs.ShouldAdvanceIT,
              PSTATE := s.regs.PSTATE, PMULastThresholdValue := s.regs.PMULastThresholdValue,
              PMUEventAccumulator := s.regs.PMUEventAccumulator, VariantImplemented := s.regs.VariantImplemented,
              FeatureImpl := s.regs.FeatureImpl, bank_BitVec_32 := s.regs.bank_BitVec_32,
              bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
              bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
              bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32, bank_BitVec_64 := s.regs.bank_BitVec_64,
              bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
              bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
              bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31, bank_Bool := s.regs.bank_Bool,
              bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1), bank_BitVec_1 := s.regs.bank_BitVec_1,
              bank_BitVec_56 := s.regs.bank_BitVec_56, bank_BitVec_16 := s.regs.bank_BitVec_16,
              bank_BitVec_4 := s.regs.bank_BitVec_4, bank_BitVec_128 := s.regs.bank_BitVec_128,
              bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32,
              bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
              bank_Option_InterruptID := s.regs.bank_Option_InterruptID, bank_BitVec_8 := s.regs.bank_BitVec_8,
              bank_BitVec_2 := s.regs.bank_BitVec_2, bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
              bank_Signal := s.regs.bank_Signal },
          choiceState := s.choiceState, choiceOcc := s.choiceOcc, mem := s.mem, tags := s.tags,
          cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events }
        (ArmFull.Functions.TakePendingInterrupts
          { take_SE := Bool.true, take_vSE := Bool.true, take_IRQ := Bool.true, take_vIRQ := Bool.true,
            take_FIQ := Bool.true, take_vFIQ := Bool.true,
            iesb_req :=
              Sail.ConcurrencyInterfaceV1.oracleChoiceSource.chooseAt Sail.Primitive.bool
                ((Sail.ConcurrencyInterfaceV1.ChoiceLabel.site 7640).child 6) s.choiceState }
          {
            regs :=
              { gpr := s.regs.gpr, __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
                PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1, SPESampleCounter := s.regs.SPESampleCounter,
                SPERecordData := s.regs.SPERecordData, SP_EL3 := s.regs.SP_EL3, SP_EL2 := s.regs.SP_EL2,
                SP_EL1 := s.regs.SP_EL1, SP_EL0 := s.regs.SP_EL0, __mpam_vpmr_max := s.regs.__mpam_vpmr_max,
                __BranchTaken := s.regs.__BranchTaken, Branchtypetaken := s.regs.Branchtypetaken,
                __ThisInstrEnc := s.regs.__ThisInstrEnc, __SPE_LFSR := s.regs.__SPE_LFSR,
                SPESampleOpType := s.regs.SPESampleOpType, TSTATE := s.regs.TSTATE, FPSR := s.regs.FPSR,
                FPCR := s.regs.FPCR, _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA, _FFR := s.regs._FFR, _P := s.regs._P,
                _Z := s.regs._Z, BTypeCompatible := s.regs.BTypeCompatible, BTypeNext := s.regs.BTypeNext,
                RC := s.regs.RC, PhysicalCount := s.regs.PhysicalCount, _PC := s.regs._PC,
                ShouldAdvanceSS := s.regs.ShouldAdvanceSS, ShouldAdvanceIT := s.regs.ShouldAdvanceIT,
                PSTATE := s.regs.PSTATE, PMULastThresholdValue := s.regs.PMULastThresholdValue,
                PMUEventAccumulator := s.regs.PMUEventAccumulator, VariantImplemented := s.regs.VariantImplemented,
                FeatureImpl := s.regs.FeatureImpl, bank_BitVec_32 := s.regs.bank_BitVec_32,
                bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
                bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
                bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32, bank_BitVec_64 := s.regs.bank_BitVec_64,
                bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
                bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
                bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31, bank_Bool := s.regs.bank_Bool,
                bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1), bank_BitVec_1 := s.regs.bank_BitVec_1,
                bank_BitVec_56 := s.regs.bank_BitVec_56, bank_BitVec_16 := s.regs.bank_BitVec_16,
                bank_BitVec_4 := s.regs.bank_BitVec_4, bank_BitVec_128 := s.regs.bank_BitVec_128,
                bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32,
                bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
                bank_Option_InterruptID := s.regs.bank_Option_InterruptID, bank_BitVec_8 := s.regs.bank_BitVec_8,
                bank_BitVec_2 := s.regs.bank_BitVec_2, bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
                bank_Signal := s.regs.bank_Signal },
            choiceState := s.choiceState, choiceOcc := s.choiceOcc, mem := s.mem, tags := s.tags,
            cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events }),
    mem := s.mem, tags := s.tags, cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events }

def beforeFetchState : NativeState → NativeState :=
fun s =>
  {
    regs :=
      { gpr := s.regs.gpr, __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
        PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1, SPESampleCounter := s.regs.SPESampleCounter,
        SPERecordData := s.regs.SPERecordData, SP_EL3 := s.regs.SP_EL3, SP_EL2 := s.regs.SP_EL2,
        SP_EL1 := s.regs.SP_EL1, SP_EL0 := s.regs.SP_EL0, __mpam_vpmr_max := s.regs.__mpam_vpmr_max,
        __BranchTaken := s.regs.__BranchTaken, Branchtypetaken := s.regs.Branchtypetaken,
        __ThisInstrEnc := s.regs.__ThisInstrEnc, __SPE_LFSR := s.regs.__SPE_LFSR,
        SPESampleOpType := s.regs.SPESampleOpType, TSTATE := s.regs.TSTATE, FPSR := s.regs.FPSR, FPCR := s.regs.FPCR,
        _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA, _FFR := s.regs._FFR, _P := s.regs._P, _Z := s.regs._Z,
        BTypeCompatible := s.regs.BTypeCompatible, BTypeNext := s.regs.BTypeNext, RC := s.regs.RC,
        PhysicalCount := s.regs.PhysicalCount, _PC := s.regs._PC, ShouldAdvanceSS := Bool.true,
        ShouldAdvanceIT := Bool.false, PSTATE := s.regs.PSTATE, PMULastThresholdValue := s.regs.PMULastThresholdValue,
        PMUEventAccumulator := s.regs.PMUEventAccumulator, VariantImplemented := s.regs.VariantImplemented,
        FeatureImpl := s.regs.FeatureImpl,
        bank_BitVec_32 :=
          s.regs.bank_BitVec_32.set ArmFull.Bank_BitVec_32._EDSCR
            (ArmFull.Functions._update_EDSCR_Type_PipeAdv
              (Sail.BitVec.updateSubrange (s.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32._EDSCR) 30 29
                (Sail.BitVec.slice (s.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDCCSR_EL0) 29 2))
              (BitVec.ofNat 1 1)),
        bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
        bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
        bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32,
        bank_BitVec_64 :=
          s.regs.bank_BitVec_64.set ArmFull.Bank_BitVec_64.MDCCSR_EL0
            (Sail.BitVec.updateSubrange (s.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDCCSR_EL0) 30 29
              (Sail.BitVec.slice
                (ArmFull.Functions._update_EDSCR_Type_PipeAdv
                  (Sail.BitVec.updateSubrange (s.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32._EDSCR) 30 29
                    (Sail.BitVec.slice (s.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDCCSR_EL0) 29 2))
                  (BitVec.ofNat 1 1))
                29 2)),
        bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
        bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
        bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31, bank_Bool := s.regs.bank_Bool,
        bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1), bank_BitVec_1 := s.regs.bank_BitVec_1,
        bank_BitVec_56 := s.regs.bank_BitVec_56, bank_BitVec_16 := s.regs.bank_BitVec_16,
        bank_BitVec_4 := s.regs.bank_BitVec_4, bank_BitVec_128 := s.regs.bank_BitVec_128,
        bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32, bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
        bank_Option_InterruptID := s.regs.bank_Option_InterruptID, bank_BitVec_8 := s.regs.bank_BitVec_8,
        bank_BitVec_2 := s.regs.bank_BitVec_2, bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
        bank_Signal := s.regs.bank_Signal },
    choiceState :=
      ArmBridge.CruxCore.resCS
        {
          regs :=
            { gpr := s.regs.gpr, __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
              PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1, SPESampleCounter := s.regs.SPESampleCounter,
              SPERecordData := s.regs.SPERecordData, SP_EL3 := s.regs.SP_EL3, SP_EL2 := s.regs.SP_EL2,
              SP_EL1 := s.regs.SP_EL1, SP_EL0 := s.regs.SP_EL0, __mpam_vpmr_max := s.regs.__mpam_vpmr_max,
              __BranchTaken := s.regs.__BranchTaken, Branchtypetaken := s.regs.Branchtypetaken,
              __ThisInstrEnc := s.regs.__ThisInstrEnc, __SPE_LFSR := s.regs.__SPE_LFSR,
              SPESampleOpType := s.regs.SPESampleOpType, TSTATE := s.regs.TSTATE, FPSR := s.regs.FPSR,
              FPCR := s.regs.FPCR, _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA, _FFR := s.regs._FFR, _P := s.regs._P,
              _Z := s.regs._Z, BTypeCompatible := s.regs.BTypeCompatible, BTypeNext := s.regs.BTypeNext,
              RC := s.regs.RC, PhysicalCount := s.regs.PhysicalCount, _PC := s.regs._PC,
              ShouldAdvanceSS := s.regs.ShouldAdvanceSS, ShouldAdvanceIT := s.regs.ShouldAdvanceIT,
              PSTATE := s.regs.PSTATE, PMULastThresholdValue := s.regs.PMULastThresholdValue,
              PMUEventAccumulator := s.regs.PMUEventAccumulator, VariantImplemented := s.regs.VariantImplemented,
              FeatureImpl := s.regs.FeatureImpl, bank_BitVec_32 := s.regs.bank_BitVec_32,
              bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
              bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
              bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32, bank_BitVec_64 := s.regs.bank_BitVec_64,
              bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
              bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
              bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31, bank_Bool := s.regs.bank_Bool,
              bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1), bank_BitVec_1 := s.regs.bank_BitVec_1,
              bank_BitVec_56 := s.regs.bank_BitVec_56, bank_BitVec_16 := s.regs.bank_BitVec_16,
              bank_BitVec_4 := s.regs.bank_BitVec_4, bank_BitVec_128 := s.regs.bank_BitVec_128,
              bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32,
              bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
              bank_Option_InterruptID := s.regs.bank_Option_InterruptID, bank_BitVec_8 := s.regs.bank_BitVec_8,
              bank_BitVec_2 := s.regs.bank_BitVec_2, bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
              bank_Signal := s.regs.bank_Signal },
          choiceState := s.choiceState, choiceOcc := s.choiceOcc, mem := s.mem, tags := s.tags,
          cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events }
        (ArmFull.Functions.TakePendingInterrupts
          { take_SE := Bool.true, take_vSE := Bool.true, take_IRQ := Bool.true, take_vIRQ := Bool.true,
            take_FIQ := Bool.true, take_vFIQ := Bool.true,
            iesb_req :=
              Sail.ConcurrencyInterfaceV1.oracleChoiceSource.chooseAt Sail.Primitive.bool
                ((Sail.ConcurrencyInterfaceV1.ChoiceLabel.site 7640).child 6) s.choiceState }
          {
            regs :=
              { gpr := s.regs.gpr, __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
                PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1, SPESampleCounter := s.regs.SPESampleCounter,
                SPERecordData := s.regs.SPERecordData, SP_EL3 := s.regs.SP_EL3, SP_EL2 := s.regs.SP_EL2,
                SP_EL1 := s.regs.SP_EL1, SP_EL0 := s.regs.SP_EL0, __mpam_vpmr_max := s.regs.__mpam_vpmr_max,
                __BranchTaken := s.regs.__BranchTaken, Branchtypetaken := s.regs.Branchtypetaken,
                __ThisInstrEnc := s.regs.__ThisInstrEnc, __SPE_LFSR := s.regs.__SPE_LFSR,
                SPESampleOpType := s.regs.SPESampleOpType, TSTATE := s.regs.TSTATE, FPSR := s.regs.FPSR,
                FPCR := s.regs.FPCR, _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA, _FFR := s.regs._FFR, _P := s.regs._P,
                _Z := s.regs._Z, BTypeCompatible := s.regs.BTypeCompatible, BTypeNext := s.regs.BTypeNext,
                RC := s.regs.RC, PhysicalCount := s.regs.PhysicalCount, _PC := s.regs._PC,
                ShouldAdvanceSS := s.regs.ShouldAdvanceSS, ShouldAdvanceIT := s.regs.ShouldAdvanceIT,
                PSTATE := s.regs.PSTATE, PMULastThresholdValue := s.regs.PMULastThresholdValue,
                PMUEventAccumulator := s.regs.PMUEventAccumulator, VariantImplemented := s.regs.VariantImplemented,
                FeatureImpl := s.regs.FeatureImpl, bank_BitVec_32 := s.regs.bank_BitVec_32,
                bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
                bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
                bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32, bank_BitVec_64 := s.regs.bank_BitVec_64,
                bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
                bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
                bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31, bank_Bool := s.regs.bank_Bool,
                bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1), bank_BitVec_1 := s.regs.bank_BitVec_1,
                bank_BitVec_56 := s.regs.bank_BitVec_56, bank_BitVec_16 := s.regs.bank_BitVec_16,
                bank_BitVec_4 := s.regs.bank_BitVec_4, bank_BitVec_128 := s.regs.bank_BitVec_128,
                bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32,
                bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
                bank_Option_InterruptID := s.regs.bank_Option_InterruptID, bank_BitVec_8 := s.regs.bank_BitVec_8,
                bank_BitVec_2 := s.regs.bank_BitVec_2, bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
                bank_Signal := s.regs.bank_Signal },
            choiceState := s.choiceState, choiceOcc := s.choiceOcc, mem := s.mem, tags := s.tags,
            cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events }),
    choiceOcc :=
      ArmBridge.CruxCore.resCO
        {
          regs :=
            { gpr := s.regs.gpr, __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
              PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1, SPESampleCounter := s.regs.SPESampleCounter,
              SPERecordData := s.regs.SPERecordData, SP_EL3 := s.regs.SP_EL3, SP_EL2 := s.regs.SP_EL2,
              SP_EL1 := s.regs.SP_EL1, SP_EL0 := s.regs.SP_EL0, __mpam_vpmr_max := s.regs.__mpam_vpmr_max,
              __BranchTaken := s.regs.__BranchTaken, Branchtypetaken := s.regs.Branchtypetaken,
              __ThisInstrEnc := s.regs.__ThisInstrEnc, __SPE_LFSR := s.regs.__SPE_LFSR,
              SPESampleOpType := s.regs.SPESampleOpType, TSTATE := s.regs.TSTATE, FPSR := s.regs.FPSR,
              FPCR := s.regs.FPCR, _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA, _FFR := s.regs._FFR, _P := s.regs._P,
              _Z := s.regs._Z, BTypeCompatible := s.regs.BTypeCompatible, BTypeNext := s.regs.BTypeNext,
              RC := s.regs.RC, PhysicalCount := s.regs.PhysicalCount, _PC := s.regs._PC,
              ShouldAdvanceSS := s.regs.ShouldAdvanceSS, ShouldAdvanceIT := s.regs.ShouldAdvanceIT,
              PSTATE := s.regs.PSTATE, PMULastThresholdValue := s.regs.PMULastThresholdValue,
              PMUEventAccumulator := s.regs.PMUEventAccumulator, VariantImplemented := s.regs.VariantImplemented,
              FeatureImpl := s.regs.FeatureImpl, bank_BitVec_32 := s.regs.bank_BitVec_32,
              bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
              bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
              bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32, bank_BitVec_64 := s.regs.bank_BitVec_64,
              bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
              bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
              bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31, bank_Bool := s.regs.bank_Bool,
              bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1), bank_BitVec_1 := s.regs.bank_BitVec_1,
              bank_BitVec_56 := s.regs.bank_BitVec_56, bank_BitVec_16 := s.regs.bank_BitVec_16,
              bank_BitVec_4 := s.regs.bank_BitVec_4, bank_BitVec_128 := s.regs.bank_BitVec_128,
              bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32,
              bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
              bank_Option_InterruptID := s.regs.bank_Option_InterruptID, bank_BitVec_8 := s.regs.bank_BitVec_8,
              bank_BitVec_2 := s.regs.bank_BitVec_2, bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
              bank_Signal := s.regs.bank_Signal },
          choiceState := s.choiceState, choiceOcc := s.choiceOcc, mem := s.mem, tags := s.tags,
          cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events }
        (ArmFull.Functions.TakePendingInterrupts
          { take_SE := Bool.true, take_vSE := Bool.true, take_IRQ := Bool.true, take_vIRQ := Bool.true,
            take_FIQ := Bool.true, take_vFIQ := Bool.true,
            iesb_req :=
              Sail.ConcurrencyInterfaceV1.oracleChoiceSource.chooseAt Sail.Primitive.bool
                ((Sail.ConcurrencyInterfaceV1.ChoiceLabel.site 7640).child 6) s.choiceState }
          {
            regs :=
              { gpr := s.regs.gpr, __emulator_termination_opcode := s.regs.__emulator_termination_opcode,
                PMEVCNTSVR_EL1 := s.regs.PMEVCNTSVR_EL1, SPESampleCounter := s.regs.SPESampleCounter,
                SPERecordData := s.regs.SPERecordData, SP_EL3 := s.regs.SP_EL3, SP_EL2 := s.regs.SP_EL2,
                SP_EL1 := s.regs.SP_EL1, SP_EL0 := s.regs.SP_EL0, __mpam_vpmr_max := s.regs.__mpam_vpmr_max,
                __BranchTaken := s.regs.__BranchTaken, Branchtypetaken := s.regs.Branchtypetaken,
                __ThisInstrEnc := s.regs.__ThisInstrEnc, __SPE_LFSR := s.regs.__SPE_LFSR,
                SPESampleOpType := s.regs.SPESampleOpType, TSTATE := s.regs.TSTATE, FPSR := s.regs.FPSR,
                FPCR := s.regs.FPCR, _ZT0 := s.regs._ZT0, _ZA := s.regs._ZA, _FFR := s.regs._FFR, _P := s.regs._P,
                _Z := s.regs._Z, BTypeCompatible := s.regs.BTypeCompatible, BTypeNext := s.regs.BTypeNext,
                RC := s.regs.RC, PhysicalCount := s.regs.PhysicalCount, _PC := s.regs._PC,
                ShouldAdvanceSS := s.regs.ShouldAdvanceSS, ShouldAdvanceIT := s.regs.ShouldAdvanceIT,
                PSTATE := s.regs.PSTATE, PMULastThresholdValue := s.regs.PMULastThresholdValue,
                PMUEventAccumulator := s.regs.PMUEventAccumulator, VariantImplemented := s.regs.VariantImplemented,
                FeatureImpl := s.regs.FeatureImpl, bank_BitVec_32 := s.regs.bank_BitVec_32,
                bank_Vector_BitVec_32_16 := s.regs.bank_Vector_BitVec_32_16,
                bank_Vector_BitVec_32_4 := s.regs.bank_Vector_BitVec_32_4,
                bank_Vector_BitVec_64_32 := s.regs.bank_Vector_BitVec_64_32, bank_BitVec_64 := s.regs.bank_BitVec_64,
                bank_Vector_BitVec_64_16 := s.regs.bank_Vector_BitVec_64_16,
                bank_Vector_BitVec_64_4 := s.regs.bank_Vector_BitVec_64_4,
                bank_Vector_BitVec_32_31 := s.regs.bank_Vector_BitVec_32_31, bank_Bool := s.regs.bank_Bool,
                bank_Int := s.regs.bank_Int.set ArmFull.Bank_Int.SEE (-1), bank_BitVec_1 := s.regs.bank_BitVec_1,
                bank_BitVec_56 := s.regs.bank_BitVec_56, bank_BitVec_16 := s.regs.bank_BitVec_16,
                bank_BitVec_4 := s.regs.bank_BitVec_4, bank_BitVec_128 := s.regs.bank_BitVec_128,
                bank_Vector_Bool_32 := s.regs.bank_Vector_Bool_32,
                bank_Vector_BitVec_64_64 := s.regs.bank_Vector_BitVec_64_64,
                bank_Option_InterruptID := s.regs.bank_Option_InterruptID, bank_BitVec_8 := s.regs.bank_BitVec_8,
                bank_BitVec_2 := s.regs.bank_BitVec_2, bank_Vector_BitVec_64_7 := s.regs.bank_Vector_BitVec_64_7,
                bank_Signal := s.regs.bank_Signal },
            choiceState := s.choiceState, choiceOcc := s.choiceOcc, mem := s.mem, tags := s.tags,
            cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events }),
    mem := s.mem, tags := s.tags, cycleCount := s.cycleCount, sailOutput := s.sailOutput, events := s.events }

def nativeTail : ∀ (real : Type) [Sail.SailReal real],
    NativeState → BitVec 32 → __InstrEnc → NativeState →
      EStateM.Result (Sail.Error exception) NativeState Unit :=
fun real [Sail.SailReal real] s w enc0 afterFetch =>
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
            (ArmFull.Functions.PMUEvent ArmFull.Functions.PMU_EVENT_INST_SPEC afterFetch)
            (fun a s' =>
              ArmBridge.CruxCore.bind_app.match_1
                (fun x =>
                  EStateM.Result (Sail.Error ArmFull.exception)
                    (Sail.ConcurrencyInterfaceV1.SequentialState ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource)
                    Unit)
                (ArmFull.Functions.__DefaultCond ArmFull.__InstrEnc.__A64
                  {
                    regs :=
                      ArmFull.Register.__ExclusiveMonitorSet.set Bool.false
                        (ArmFull.Register.__BranchTaken.set Bool.false s'.regs),
                    choiceState := s'.choiceState, choiceOcc := s'.choiceOcc, mem := s'.mem, tags := s'.tags,
                    cycleCount := s'.cycleCount, sailOutput := s'.sailOutput, events := s'.events })
                (fun a s' =>
                  ArmBridge.CruxCore.bind_app.match_1
                    (fun x =>
                      EStateM.Result (Sail.Error ArmFull.exception)
                        (Sail.ConcurrencyInterfaceV1.SequentialState ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource)
                        Unit)
                    (ArmFull.Functions.__SetThisInstrDetails ArmFull.__InstrEnc.__A64 w a s')
                    (fun a s' =>
                      ArmBridge.CruxCore.bind_app.match_1
                        (fun x =>
                          EStateM.Result (Sail.Error ArmFull.exception)
                            (Sail.ConcurrencyInterfaceV1.SequentialState ArmFull.Regs
                              Sail.ConcurrencyInterfaceV1.oracleChoiceSource)
                            Unit)
                        (ArmFull.Functions.SPEPreExecution Unit.unit s')
                        (fun a s' =>
                          ArmBridge.CruxCore.bind_app.match_1
                            (fun x =>
                              EStateM.Result (Sail.Error ArmFull.exception)
                                (Sail.ConcurrencyInterfaceV1.SequentialState ArmFull.Regs
                                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource)
                                Unit)
                            (ArmFull.Functions.__DecodeExecute ArmFull.__InstrEnc.__A64 w s')
                            (fun a s' => ArmFull.Functions.PMUEvent ArmFull.Functions.PMU_EVENT_INST_RETIRED s')
                            fun e s' => EStateM.Result.error e s')
                        fun e s' => EStateM.Result.error e s')
                    fun e s' => EStateM.Result.error e s')
                fun e s' => EStateM.Result.error e s')
            fun e s' => EStateM.Result.error e s')
          (fun a s' => EStateM.Result.ok a s')
          (fun u s' =>
            cond
              (((ArmFull.Functions.IsSEE u).or (ArmFull.Functions.IsUNDEFINED u)).or
                (ArmFull.Functions.IsUNPREDICTABLE u))
              (Bind.bind (ArmFull.Functions.UsingAArch32 Unit.unit) fun w__7 =>
                cond w__7
                  (ArmFull.Functions.__InstructionExecute.match_2 (fun enc => ArmFull.SailM Unit) enc0
                    (fun _ =>
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
                    (fun _ =>
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
                    (fun _ =>
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
                  { regs := ArmFull.Register.InGuardedPage.set Bool.false s'.regs, choiceState := s'.choiceState,
                    choiceOcc := s'.choiceOcc, mem := s'.mem, tags := s'.tags, cycleCount := s'.cycleCount,
                    sailOutput := s'.sailOutput, events := s'.events })
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
                      Bind.bind (ArmFull.readReg ArmFull.Register.__BranchTaken) fun w__11 =>
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
                    (Bind.bind (ArmFull.readReg ArmFull.Register.__BranchTaken) fun w__11 =>
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
          (fun _ => EStateM.pure Unit.unit) (fun e => ArmFull.sailThrow e) s')
      fun e s' => EStateM.Result.error e s')
    (fun a s => ArmFull.Functions.__CycleEnd Unit.unit s) fun e s' => EStateM.Result.error e s'

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.prefetch_boundary"
  (← IO.getStderr).flush

theorem prefetch_boundary (real : Type) [Sail.SailReal real] (s : NativeState)
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
 :
    ∃ (enc0 : __InstrEnc) (t0 fetched : NativeState),
      t0.regs = preFetchRegs s.regs ∧ t0.mem = s.mem ∧ t0.events = s.events ∧
      (__FetchInstr s.regs._PC : SailM (__InstrEnc × BitVec 32)) t0 = .ok (.__A64, w) fetched ∧
      fetched.regs = clrGP (fetchRegs t0.regs) ∧ fetched.mem = t0.mem ∧
      modelStep real s = nativeTail real s w enc0 fetched := by
  obtain ⟨fL, fS, fO, fC, fSO, hFetch⟩ := fetch_fns s w hFS
  obtain ⟨enc0, henc⟩ := uenc (ChoiceLabel.site 7637) (encodingState s)
  dsimp only [encodingState] at henc
  let t0 := beforeFetchState s
  let fetched : NativeState :=
    { t0 with regs := clrGP (fetchRegs t0.regs), events := t0.events ++ fL t0, choiceState := fS t0, choiceOcc := fO t0, cycleCount := fC t0, sailOutput := fSO t0 }
  refine ⟨enc0, t0, fetched, rfl, rfl, rfl, hFetch t0 rfl rfl rfl, rfl, rfl, ?_⟩
  unfold modelStep __TopLevel
  simp only [ArmBridge.Awc.ite_cond]
  simp only [bind, EStateM.bind, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply,
    Sail.ConcurrencyInterfaceV1.PreSail.writeReg_apply, ArmBridge.BKmin.Halted, ubool]
  simp only [BK3_Halted.native]
  simp (config := {decide := true}) only [bind, EStateM.bind, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply, hST,
    ArmFull.Register.SEE, ArmFull.Register._EDSCR, ite_true, ite_false, Bool.false_eq_true, reduceIte, Bool.not_false, Bool.not_true]
  have hST' : Sail.BitVec.extractLsb (s.regs.bank_BitVec_32 ._EDSCR) 5 0 = 2#6 := by
    simpa [_get_EDSCR_Type_STATUS] using hST
  simp (config := {decide := true}) only [Regs.ref_Int, hST', reduceIte, ite_true, ite_false, Bool.false_eq_true,
    Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, decide_false, decide_true,
    BitVec.reduceBEq, BitVec.reduceEq, beq_self_eq_true, Bool.not_true, Bool.cond_false, Bool.cond_true]
  simp only [undefined_InterruptReq, bind, EStateM.bind, ubool, pure, EStateM.pure]
  rw [tc_apply]
  simp only [EStateM.bind]
  rw [tpi_frame]
  rotate_left
  all_goals first
    | (simp only [SEE, Regs.ref_Int, hF4, hEL, hnRW, hE2H, hTGE, hGIC, hDA, hDI, hDF]; done)
    | skip
  simp only [Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply, Bool.not_false, ite_true, EStateM.bind, Bool.cond_true, Bool.cond_false, Bool.not_false]
  simp only [Branchtypetaken, Regs.ref_Int]
  have hBT' : (s.regs.Branchtypetaken == BranchType.BranchType_RESET) = false := by
    revert hBT; cases s.regs.Branchtypetaken <;> intro h1 <;> first | exact absurd rfl h1 | rfl
  simp only [hBT', Bool.cond_false]
  unfold __InstructionExecute
  simp only [ArmBridge.Awc.ite_cond]
  simp only [↓bind_app]
  erw [henc]
  simp only [ubv, ArmBridge.BKmin.EDSCRread, BK3_EDSCRread.native, ArmBridge.BKmin.EDSCRwritePipeAdv,
    BK3_EDSCRwritePipeAdv.native, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply]
  have hZ : IsZero (0#32) = true := by decide
  simp only [EDESR, Regs.ref_BitVec_32, ArmFull.Register._EDSCR, ArmFull.Register.MDCCSR_EL0, Regs.ref_BitVec_64]
  simp (disch := decide) only [Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same,
    hEDESR, hZ, Bool.not_true, Bool.cond_false]
  simp only [↓bind_app]
  rw [tc_apply]
  simp only [↓bind_app, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply, Sail.ConcurrencyInterfaceV1.PreSail.writeReg_apply,
    pure, EStateM.pure, PSTATE, ShouldAdvanceIT, ShouldAdvanceSS, hnRW, ArmBridge.BKmin.ThisInstrAddr64, BK3_ThisInstrAddr64.native]
  simp (config := {decide := true}) only [hnRW, BitVec.reduceBEq, Bool.cond_false, Bool.cond_true, beq_self_eq_true,
    ↓bind_app, EStateM.pure, pure, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply,
    Sail.ConcurrencyInterfaceV1.PreSail.writeReg_apply]
  rw [pc_id]
  rw [hFetch _ ?f1 ?f2 ?f3]
  case f1 => rfl
  case f2 => rfl
  case f3 => rfl
  simp only []
  rw [ArmBridge.BKmin.emu (real := real) _ _ _ (by simp [fetchRegs, clrGP, hEmu])]
  simp only [ArmBridge.BKv.emu_native]
  unfold nativeTail
  dsimp only [t0, fetched, beforeFetchState]

#print axioms prefetch_boundary
end ArmBridge.CruxGenGuarded
