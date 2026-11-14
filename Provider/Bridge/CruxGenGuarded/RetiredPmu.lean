import Bridge.CruxGenGuarded.Action
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! GENERATED internal retired-PMU composition. Its actual primitive-success
fact must be supplied by the fixed Q-domain native-owner theorem. -/

def nativeAfterRetired : NativeState → EStateM.Result (Sail.Error exception) NativeState Unit :=
fun afterRetired =>
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
        (ArmFull.Functions.SPEPostExecution Unit.unit afterRetired)
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
                    bank_Option_InterruptID := s'.regs.bank_Option_InterruptID, bank_BitVec_8 := s'.regs.bank_BitVec_8,
                    bank_BitVec_2 := s'.regs.bank_BitVec_2, bank_Vector_BitVec_64_7 := s'.regs.bank_Vector_BitVec_64_7,
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
                            SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR, FPCR := r.FPCR,
                            _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P, _Z := r._Z,
                            BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext, RC := r.RC,
                            PhysicalCount := r.PhysicalCount, _PC := r._PC, ShouldAdvanceSS := r.ShouldAdvanceSS,
                            ShouldAdvanceIT := r.ShouldAdvanceIT, PSTATE := v,
                            PMULastThresholdValue := r.PMULastThresholdValue,
                            PMUEventAccumulator := r.PMUEventAccumulator, VariantImplemented := r.VariantImplemented,
                            FeatureImpl := r.FeatureImpl, bank_BitVec_32 := r.bank_BitVec_32,
                            bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                            bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                            bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32, bank_BitVec_64 := r.bank_BitVec_64,
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
                              SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR, FPCR := r.FPCR,
                              _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P, _Z := r._Z,
                              BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext, RC := r.RC,
                              PhysicalCount := r.PhysicalCount, _PC := r._PC, ShouldAdvanceSS := r.ShouldAdvanceSS,
                              ShouldAdvanceIT := r.ShouldAdvanceIT, PSTATE := v,
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
                              bank_Signal := r.bank_Signal } }
                        { N := w__9.N, Z := w__9.Z, C := w__9.C, V := w__9.V, D := w__9.D, A := w__9.A, I := w__9.I,
                          F := w__9.F, EXLOCK := w__9.EXLOCK, PAN := w__9.PAN, UAO := w__9.UAO, DIT := w__9.DIT,
                          TCO := w__9.TCO, PM := w__9.PM, PPEND := w__9.PPEND, BTYPE := w__10, ZA := w__9.ZA,
                          SM := w__9.SM, ALLINT := w__9.ALLINT, SS := w__9.SS, IL := w__9.IL, EL := w__9.EL,
                          nRW := w__9.nRW, SP := w__9.SP, Q := w__9.Q, GE := w__9.GE, SSBS := w__9.SSBS, IT := w__9.IT,
                          J := w__9.J, T := w__9.T, E := w__9.E, M := w__9.M })
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
                            bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32, bank_BitVec_64 := r.bank_BitVec_64,
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
                              (Sail.BitVec.extractLsb (Sail.BitVec.addInt w__12 (ArmFull.Functions.fdiv_int w__13 8)) 63
                                0))
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
                              fun w__15 => cond w__15 (ArmFull.Functions.SSAdvance Unit.unit) (EStateM.pure Unit.unit)))
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
                                bank_Option_InterruptID := r.bank_Option_InterruptID, bank_BitVec_8 := r.bank_BitVec_8,
                                bank_BitVec_2 := r.bank_BitVec_2, bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
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
                              fun w__15 => cond w__15 (ArmFull.Functions.SSAdvance Unit.unit) (EStateM.pure Unit.unit))
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
                            fun w__15 => cond w__15 (ArmFull.Functions.SSAdvance Unit.unit) (EStateM.pure Unit.unit))))
                (Bind.bind
                  (ArmFull.readReg
                    { get := fun r => r.__BranchTaken,
                      set := fun v r =>
                        { gpr := r.gpr, __emulator_termination_opcode := r.__emulator_termination_opcode,
                          PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1, SPESampleCounter := r.SPESampleCounter,
                          SPERecordData := r.SPERecordData, SP_EL3 := r.SP_EL3, SP_EL2 := r.SP_EL2, SP_EL1 := r.SP_EL1,
                          SP_EL0 := r.SP_EL0, __mpam_vpmr_max := r.__mpam_vpmr_max, __BranchTaken := v,
                          Branchtypetaken := r.Branchtypetaken, __ThisInstrEnc := r.__ThisInstrEnc,
                          __SPE_LFSR := r.__SPE_LFSR, SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE,
                          FPSR := r.FPSR, FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P,
                          _Z := r._Z, BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext, RC := r.RC,
                          PhysicalCount := r.PhysicalCount, _PC := r._PC, ShouldAdvanceSS := r.ShouldAdvanceSS,
                          ShouldAdvanceIT := r.ShouldAdvanceIT, PSTATE := r.PSTATE,
                          PMULastThresholdValue := r.PMULastThresholdValue,
                          PMUEventAccumulator := r.PMUEventAccumulator, VariantImplemented := r.VariantImplemented,
                          FeatureImpl := r.FeatureImpl, bank_BitVec_32 := r.bank_BitVec_32,
                          bank_Vector_BitVec_32_16 := r.bank_Vector_BitVec_32_16,
                          bank_Vector_BitVec_32_4 := r.bank_Vector_BitVec_32_4,
                          bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32, bank_BitVec_64 := r.bank_BitVec_64,
                          bank_Vector_BitVec_64_16 := r.bank_Vector_BitVec_64_16,
                          bank_Vector_BitVec_64_4 := r.bank_Vector_BitVec_64_4,
                          bank_Vector_BitVec_32_31 := r.bank_Vector_BitVec_32_31, bank_Bool := r.bank_Bool,
                          bank_Int := r.bank_Int, bank_BitVec_1 := r.bank_BitVec_1, bank_BitVec_56 := r.bank_BitVec_56,
                          bank_BitVec_16 := r.bank_BitVec_16, bank_BitVec_4 := r.bank_BitVec_4,
                          bank_BitVec_128 := r.bank_BitVec_128, bank_Vector_Bool_32 := r.bank_Vector_Bool_32,
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
                            (Sail.BitVec.extractLsb (Sail.BitVec.addInt w__12 (ArmFull.Functions.fdiv_int w__13 8)) 63
                              0))
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
                                bank_Option_InterruptID := r.bank_Option_InterruptID, bank_BitVec_8 := r.bank_BitVec_8,
                                bank_BitVec_2 := r.bank_BitVec_2, bank_Vector_BitVec_64_7 := r.bank_Vector_BitVec_64_7,
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
                              fun w__15 => cond w__15 (ArmFull.Functions.SSAdvance Unit.unit) (EStateM.pure Unit.unit))
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
                            fun w__15 => cond w__15 (ArmFull.Functions.SSAdvance Unit.unit) (EStateM.pure Unit.unit)))
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
                              SPESampleOpType := r.SPESampleOpType, TSTATE := r.TSTATE, FPSR := r.FPSR, FPCR := r.FPCR,
                              _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P, _Z := r._Z,
                              BTypeCompatible := r.BTypeCompatible, BTypeNext := r.BTypeNext, RC := r.RC,
                              PhysicalCount := r.PhysicalCount, _PC := r._PC, ShouldAdvanceSS := r.ShouldAdvanceSS,
                              ShouldAdvanceIT := v, PSTATE := r.PSTATE,
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
                            fun w__15 => cond w__15 (ArmFull.Functions.SSAdvance Unit.unit) (EStateM.pure Unit.unit))
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
                                  FPCR := r.FPCR, _ZT0 := r._ZT0, _ZA := r._ZA, _FFR := r._FFR, _P := r._P, _Z := r._Z,
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
                          fun w__15 => cond w__15 (ArmFull.Functions.SSAdvance Unit.unit) (EStateM.pure Unit.unit))))
                s')
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
  IO.eprintln "CURRENT_DECL CruxGenGuarded.retired_pmu_boundary"
  (← IO.getStderr).flush

theorem retired_pmu_boundary (real : Type) [Sail.SailReal real]
    (s : NativeState) (w : BitVec 32) (enc0 : __InstrEnc) (afterAction afterRetired : NativeState)
    (hPMU : (PMUEvent PMU_EVENT_INST_RETIRED : SailM Unit) afterAction = .ok () afterRetired) :
    nativeAfterAction real s w enc0 afterAction = nativeAfterRetired afterRetired := by
  unfold nativeAfterAction
  dsimp only [EStateM.bind.match_1, tc_apply.match_1, bind_app.match_1]
  erw [hPMU]
  unfold nativeAfterRetired
  dsimp only [EStateM.bind.match_1, tc_apply.match_1, bind_app.match_1]

#print axioms retired_pmu_boundary
end ArmBridge.CruxGenGuarded
