import NativeEntryCallerParts.BlPrefix
import NativeEntryCallerParts.BlrPrefix
import NativeEntryCallerParts.BranchAddr
import NativeEntryCallerParts.SpeBranch
import Bridge.CruxCore
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace NativeEntryCallerParts
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option Elab.async false

/- These are CURRENT controls; producing their final binding remains separate. -/
structure CallerControls (s : NativeState) : Prop where
  f4 : s.regs.FeatureImpl[4]! = true
  f2 : s.regs.FeatureImpl[2]! = false
  f3 : s.regs.FeatureImpl[3]! = false
  f6 : s.regs.FeatureImpl[6]! = true
  f7 : s.regs.FeatureImpl[7]! = true
  rme : s.regs.FeatureImpl[232]! = false
  vhe : s.regs.FeatureImpl[54]! = true
  brbe : s.regs.FeatureImpl[230]! = false
  el : s.regs.PSTATE.EL = 0#2
  nrw : s.regs.PSTATE.nRW = 0#1
  e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  tge : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  ns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1
  pmb : _get_PMBLIMITR_EL1_Type_E (s.regs.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1
  spe : s.regs.bank_Bool .SPESampleInFlight = false
  pmbs : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1
  nspb : _get_MDCR_EL3_Type_NSPB (s.regs.bank_BitVec_64 .MDCR_EL3) = 3#2
  nspbe : _get_MDCR_EL3_Type_NSPBE (s.regs.bank_BitVec_64 .MDCR_EL3) = 0#1
  gcsEn : _get_SCR_EL3_Type_GCSEn (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1

noncomputable def blBeforeCall : BitVec 26 → NativeState → NativeState :=
fun imm26 s =>
  @Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
    ArmFull.instArch_armFull
    (have __src :=
      @Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
        ArmFull.instArch_armFull s;
    ArmFull.Regs.mk
      (@Vector.set (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
        (@OfNat.ofNat Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
        (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
            ArmFull.instArch_armFull s).gpr
        (@Fin.val (@OfNat.ofNat Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
          (GPRSummary.key (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
        (@Sail.BitVec.zeroExtend (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
          (@Sail.BitVec.addInt (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
            (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)._PC
            (@OfNat.ofNat Int (nat_lit 4) (@instOfNat (nat_lit 4))))
          (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
        (@Fin.isLt (@OfNat.ofNat Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
          (GPRSummary.key (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))))
      __src.__emulator_termination_opcode __src.PMEVCNTSVR_EL1 __src.SPESampleCounter __src.SPERecordData __src.SP_EL3
      __src.SP_EL2 __src.SP_EL1 __src.SP_EL0 __src.__mpam_vpmr_max __src.__BranchTaken __src.Branchtypetaken
      __src.__ThisInstrEnc __src.__SPE_LFSR __src.SPESampleOpType __src.TSTATE __src.FPSR __src.FPCR __src._ZT0
      __src._ZA __src._FFR __src._P __src._Z __src.BTypeCompatible __src.BTypeNext __src.RC __src.PhysicalCount
      __src._PC __src.ShouldAdvanceSS __src.ShouldAdvanceIT __src.PSTATE __src.PMULastThresholdValue
      __src.PMUEventAccumulator __src.VariantImplemented __src.FeatureImpl __src.bank_BitVec_32
      __src.bank_Vector_BitVec_32_16 __src.bank_Vector_BitVec_32_4 __src.bank_Vector_BitVec_64_32 __src.bank_BitVec_64
      __src.bank_Vector_BitVec_64_16 __src.bank_Vector_BitVec_64_4 __src.bank_Vector_BitVec_32_31 __src.bank_Bool
      __src.bank_Int __src.bank_BitVec_1 __src.bank_BitVec_56 __src.bank_BitVec_16 __src.bank_BitVec_4
      __src.bank_BitVec_128 __src.bank_Vector_Bool_32 __src.bank_Vector_BitVec_64_64 __src.bank_Option_InterruptID
      __src.bank_BitVec_8 __src.bank_BitVec_2 __src.bank_Vector_BitVec_64_7 __src.bank_Signal)
    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
      ArmFull.instArch_armFull s)
    (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
      ArmFull.instArch_armFull s)
    (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
      ArmFull.instArch_armFull s)
    (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
      ArmFull.instArch_armFull s)
    (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
      ArmFull.instArch_armFull s)
    (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
      ArmFull.instArch_armFull s)

noncomputable def blTarget : BitVec 26 → NativeState → BitVec 64 :=
fun imm26 s =>
  @HAdd.hAdd (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
    (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
    (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
    (@instHAdd (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
      (@BitVec.instAdd (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))))
    (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
        ArmFull.instArch_armFull s)._PC
    (@sign_extend (@OfNat.ofNat Nat (nat_lit 28) (instOfNatNat (nat_lit 28)))
      (@HAppend.hAppend (BitVec (@OfNat.ofNat Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (BitVec (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (BitVec (@OfNat.ofNat Nat (nat_lit 28) (instOfNatNat (nat_lit 28))))
        (@BitVec.instHAppendHAddNat (@OfNat.ofNat Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        imm26
        (BitVec.ofNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))

theorem bl_boundary (imm26 : BitVec 26) (s : NativeState) (hp : CallerControls s) :
    (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1 : SailM Unit) s =
      (BranchTo (blTarget imm26 s) BranchType.BranchType_DIRCALL false : SailM Unit) (blBeforeCall imm26 s) := by
  simpa only [BlPrefix_native, blTarget, blBeforeCall] using
    BlPrefix_complete imm26 s hp.el hp.gcsEn (by have h := hp.f4; rwa [getElem!_pos _ 4 (by decide)] at h)

theorem bl_controls (imm26 : BitVec 26) (s : NativeState) (hp : CallerControls s) : CallerControls (blBeforeCall imm26 s) where
  f4 := hp.f4
  f2 := hp.f2
  f3 := hp.f3
  f6 := hp.f6
  f7 := hp.f7
  rme := hp.rme
  vhe := hp.vhe
  brbe := hp.brbe
  el := hp.el
  nrw := hp.nrw
  e2h := hp.e2h
  tge := hp.tge
  ns := hp.ns
  pmb := hp.pmb
  spe := hp.spe
  pmbs := hp.pmbs
  nspb := hp.nspb
  nspbe := hp.nspbe
  gcsEn := hp.gcsEn

theorem bl_btn (imm26 : BitVec 26) (s : NativeState) :
    (blBeforeCall imm26 s).regs.BTypeNext = s.regs.BTypeNext := rfl

theorem bl_PSTATE (imm26 : BitVec 26) (s : NativeState) :
    (blBeforeCall imm26 s).regs.PSTATE = s.regs.PSTATE := rfl

theorem bl__PC (imm26 : BitVec 26) (s : NativeState) :
    (blBeforeCall imm26 s).regs._PC = s.regs._PC := rfl

theorem bl_FPCR (imm26 : BitVec 26) (s : NativeState) :
    (blBeforeCall imm26 s).regs.FPCR = s.regs.FPCR := rfl

theorem bl_FPSR (imm26 : BitVec 26) (s : NativeState) :
    (blBeforeCall imm26 s).regs.FPSR = s.regs.FPSR := rfl

theorem bl__Z (imm26 : BitVec 26) (s : NativeState) :
    (blBeforeCall imm26 s).regs._Z = s.regs._Z := rfl

theorem bl_SP_EL0 (imm26 : BitVec 26) (s : NativeState) :
    (blBeforeCall imm26 s).regs.SP_EL0 = s.regs.SP_EL0 := rfl

theorem bl_mem (imm26 : BitVec 26) (s : NativeState) :
    (blBeforeCall imm26 s).mem = s.mem := rfl

theorem bl_events (imm26 : BitVec 26) (s : NativeState) :
    (blBeforeCall imm26 s).events = s.events := rfl

theorem bl_tags (imm26 : BitVec 26) (s : NativeState) :
    (blBeforeCall imm26 s).tags = s.tags := rfl

theorem bl_cycleCount (imm26 : BitVec 26) (s : NativeState) :
    (blBeforeCall imm26 s).cycleCount = s.cycleCount := rfl

theorem bl_sailOutput (imm26 : BitVec 26) (s : NativeState) :
    (blBeforeCall imm26 s).sailOutput = s.sailOutput := rfl

theorem bl_choiceState (imm26 : BitVec 26) (s : NativeState) :
    (blBeforeCall imm26 s).choiceState = s.choiceState := rfl

noncomputable def blrBeforeCall : BitVec 5 → NativeState → NativeState :=
fun Rn s =>
  @Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
    ArmFull.instArch_armFull
    (@Sail.ConcurrencyInterfaceV1.RegisterRef.set ArmFull.Regs
      (BitVec (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ArmFull.Register.BTypeNext
      (BitVec.ofNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
        ArmFull.instArch_armFull
        (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
          ArmFull.instArch_armFull
          (have __src :=
            @Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
              Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
              (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                  Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                  Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                  (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                    Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                      (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                        Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                        Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                            Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                            Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                            (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                              Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                            (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                  (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                            Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                            Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                            (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                              Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                            (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
                                instHashableNat Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                                (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                                (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                      (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s));
          ArmFull.Regs.mk
            (@Vector.set (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
              (@OfNat.ofNat Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
              (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                  (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                    Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                            Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                            Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                            (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                              Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                            (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
                                instHashableNat Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                                (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                                (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                      (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                            (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                              Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                              (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                              (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
                                instHashableNat Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                                (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                                (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                  (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
                                    instHashableNat Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                                    (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                              (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                              (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                              (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                              (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                          (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s))).gpr
              (@Fin.val (@OfNat.ofNat Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                (GPRSummary.key (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
              (@Sail.BitVec.zeroExtend (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
                (@Sail.BitVec.addInt (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
                  (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)._PC
                  (@OfNat.ofNat Int (nat_lit 4) (@instOfNat (nat_lit 4))))
                (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
              (@Fin.isLt (@OfNat.ofNat Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                (GPRSummary.key (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))))
            __src.__emulator_termination_opcode __src.PMEVCNTSVR_EL1 __src.SPESampleCounter __src.SPERecordData
            __src.SP_EL3 __src.SP_EL2 __src.SP_EL1 __src.SP_EL0 __src.__mpam_vpmr_max __src.__BranchTaken
            __src.Branchtypetaken __src.__ThisInstrEnc __src.__SPE_LFSR __src.SPESampleOpType __src.TSTATE __src.FPSR
            __src.FPCR __src._ZT0 __src._ZA __src._FFR __src._P __src._Z __src.BTypeCompatible __src.BTypeNext __src.RC
            __src.PhysicalCount __src._PC __src.ShouldAdvanceSS __src.ShouldAdvanceIT __src.PSTATE
            __src.PMULastThresholdValue __src.PMUEventAccumulator __src.VariantImplemented __src.FeatureImpl
            __src.bank_BitVec_32 __src.bank_Vector_BitVec_32_16 __src.bank_Vector_BitVec_32_4
            __src.bank_Vector_BitVec_64_32 __src.bank_BitVec_64 __src.bank_Vector_BitVec_64_16
            __src.bank_Vector_BitVec_64_4 __src.bank_Vector_BitVec_32_31 __src.bank_Bool __src.bank_Int
            __src.bank_BitVec_1 __src.bank_BitVec_56 __src.bank_BitVec_16 __src.bank_BitVec_4 __src.bank_BitVec_128
            __src.bank_Vector_Bool_32 __src.bank_Vector_BitVec_64_64 __src.bank_Option_InterruptID __src.bank_BitVec_8
            __src.bank_BitVec_2 __src.bank_Vector_BitVec_64_7 __src.bank_Signal)
          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
            (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
              ArmFull.instArch_armFull
              (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                  (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                    Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                      (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                              (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                    (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
            (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
              ArmFull.instArch_armFull
              (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                  (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                    Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                      (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                              (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                    (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
          (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
            ArmFull.instArch_armFull
            (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
              ArmFull.instArch_armFull
              (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                  (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                    Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                      (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                              (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                    (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
          (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
            ArmFull.instArch_armFull
            (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
              ArmFull.instArch_armFull
              (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                  (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                    Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                      (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                              (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                    (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
          (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
            (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
              ArmFull.instArch_armFull
              (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                  (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                    Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                      (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                              (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                    (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
          (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
            (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
              ArmFull.instArch_armFull
              (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                  (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                    Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                      (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                              (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                    (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
          (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
            (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
              ArmFull.instArch_armFull
              (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                  (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                    Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                      (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                              (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                    (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s))))))
    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
    (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1 Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
      (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
        (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
          ArmFull.instArch_armFull
          (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
            ArmFull.instArch_armFull s)
          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
          (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
            Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1 Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
            (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
              Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
            (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
            ArmFull.instArch_armFull s)
          (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
            ArmFull.instArch_armFull s)
          (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
          (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
          (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
      (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1 Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
            (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
              ArmFull.instArch_armFull
              (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
          (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
      ArmFull.instArch_armFull s)
    (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
      ArmFull.instArch_armFull s)
    (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
      ArmFull.instArch_armFull s)
    (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
      ArmFull.instArch_armFull s)
    (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
      ArmFull.instArch_armFull s)

noncomputable def blrTarget : BitVec 5 → NativeState → BitVec 64 :=
fun Rn s =>
  @Sail.BitVec.castWidth
    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
      (Sail.Int.toNatChecked (@OfNat.ofNat Int (nat_lit 63) (@instOfNat (nat_lit 63))))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
    (@Sail.BitVec.extractLsb (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
      (@GetElem.getElem
        (Vector (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
          (@OfNat.ofNat Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
        Nat (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
        (fun x i => @LT.lt Nat instLTNat i (@OfNat.ofNat Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
        (@Vector.instGetElemNatLt (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
          (@OfNat.ofNat Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
        (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
            ArmFull.instArch_armFull
            (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource
              ArmFull.instArch_armFull
              (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                  Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                  (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                    Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                      Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                      (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                    Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                    (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                      Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                      (@Sail.ConcurrencyInterfaceV1.SequentialState.mk ArmFull.Regs
                        Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.regs ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceState ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Std.ExtHashMap.insert Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                          Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                          (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                            Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                          (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@Std.ExtHashMap.getD Nat Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_1
                              Sail.ConcurrencyInterfaceV1.PreSail.occLabel._proof_2
                              (@Sail.ConcurrencyInterfaceV1.SequentialState.choiceOcc ArmFull.Regs
                                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                              (@OfNat.ofNat Nat (nat_lit 4005) (instOfNatNat (nat_lit 4005)))
                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                          Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)))
                    (@OfNat.ofNat Nat (nat_lit 4004) (instOfNatNat (nat_lit 4004)))
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sail.ConcurrencyInterfaceV1.SequentialState.mem ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.tags ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.cycleCount ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.sailOutput ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s)
              (@Sail.ConcurrencyInterfaceV1.SequentialState.events ArmFull.Regs
                Sail.ConcurrencyInterfaceV1.oracleChoiceSource ArmFull.instArch_armFull s))).gpr
        (@Fin.val (@OfNat.ofNat Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
          (GPRSummary.key (@BitVec.toNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) Rn)))
        (@Decidable.byContradiction
          (@LT.lt Nat instLTNat
            (@Fin.val (@OfNat.ofNat Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
              (GPRSummary.key (@BitVec.toNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) Rn)))
            (@OfNat.ofNat Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
          ((@Fin.val (@OfNat.ofNat Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                (GPRSummary.key (@BitVec.toNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) Rn))).decLt
            (@OfNat.ofNat Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
          fun a =>
          GPRSummary.read_complete._proof_1 (@BitVec.toNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) Rn)
            a))
      (Sail.Int.toNatChecked (@OfNat.ofNat Int (nat_lit 63) (@instOfNat (nat_lit 63))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))

theorem blr_boundary (Rn : BitVec 5) (s : NativeState) (hp : CallerControls s) (rn : Rn.toNat < 31) :
    (decode_blr_aarch64_instrs_branch_unconditional_register 0#5 Rn 0#1 0#1 1#2 0#1 : SailM Unit) s =
      (BranchTo (blrTarget Rn s) BranchType.BranchType_INDCALL false : SailM Unit) (blrBeforeCall Rn s) := by
  simpa only [BlrPrefix_native, blrTarget, blrBeforeCall] using
    BlrPrefix_complete Rn s hp.el hp.gcsEn (by have h := hp.f4; rwa [getElem!_pos _ 4 (by decide)] at h) rn

theorem blr_controls (Rn : BitVec 5) (s : NativeState) (hp : CallerControls s) : CallerControls (blrBeforeCall Rn s) where
  f4 := hp.f4
  f2 := hp.f2
  f3 := hp.f3
  f6 := hp.f6
  f7 := hp.f7
  rme := hp.rme
  vhe := hp.vhe
  brbe := hp.brbe
  el := hp.el
  nrw := hp.nrw
  e2h := hp.e2h
  tge := hp.tge
  ns := hp.ns
  pmb := hp.pmb
  spe := hp.spe
  pmbs := hp.pmbs
  nspb := hp.nspb
  nspbe := hp.nspbe
  gcsEn := hp.gcsEn

theorem blr_btn (Rn : BitVec 5) (s : NativeState) :
    (blrBeforeCall Rn s).regs.BTypeNext = 2#2 := rfl

theorem blr_PSTATE (Rn : BitVec 5) (s : NativeState) :
    (blrBeforeCall Rn s).regs.PSTATE = s.regs.PSTATE := rfl

theorem blr__PC (Rn : BitVec 5) (s : NativeState) :
    (blrBeforeCall Rn s).regs._PC = s.regs._PC := rfl

theorem blr_FPCR (Rn : BitVec 5) (s : NativeState) :
    (blrBeforeCall Rn s).regs.FPCR = s.regs.FPCR := rfl

theorem blr_FPSR (Rn : BitVec 5) (s : NativeState) :
    (blrBeforeCall Rn s).regs.FPSR = s.regs.FPSR := rfl

theorem blr__Z (Rn : BitVec 5) (s : NativeState) :
    (blrBeforeCall Rn s).regs._Z = s.regs._Z := rfl

theorem blr_SP_EL0 (Rn : BitVec 5) (s : NativeState) :
    (blrBeforeCall Rn s).regs.SP_EL0 = s.regs.SP_EL0 := rfl

theorem blr_mem (Rn : BitVec 5) (s : NativeState) :
    (blrBeforeCall Rn s).mem = s.mem := rfl

theorem blr_events (Rn : BitVec 5) (s : NativeState) :
    (blrBeforeCall Rn s).events = s.events := rfl

theorem blr_tags (Rn : BitVec 5) (s : NativeState) :
    (blrBeforeCall Rn s).tags = s.tags := rfl

theorem blr_cycleCount (Rn : BitVec 5) (s : NativeState) :
    (blrBeforeCall Rn s).cycleCount = s.cycleCount := rfl

theorem blr_sailOutput (Rn : BitVec 5) (s : NativeState) :
    (blrBeforeCall Rn s).sailOutput = s.sailOutput := rfl

theorem blr_choiceState (Rn : BitVec 5) (s : NativeState) :
    (blrBeforeCall Rn s).choiceState = s.choiceState := rfl

/- Read-only projections of the actual generated results. Both progress
equations below reduce to the original primitive equations, including choices. -/
noncomputable def nativeResultState {α : Type}
    (result : EStateM.Result (Sail.Error exception) NativeState α) : NativeState :=
  match result with
  | .ok _ t => t
  | .error _ t => t

noncomputable def addressState (target : BitVec 64) (s : NativeState) : NativeState :=
  nativeResultState (address_native target s)

noncomputable def wordResultValue
    (result : EStateM.Result (Sail.Error exception) NativeState (BitVec 64)) : BitVec 64 :=
  match result with
  | .ok value _ => value
  | .error _ _ => 0#64

noncomputable def addressValue (target : BitVec 64) (s : NativeState) : BitVec 64 :=
  wordResultValue (address_native target s)

noncomputable def speState (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) : NativeState :=
  nativeResultState (spe_native target branch conditional s)

/- The literal model supports A32 only at EL0; either actual S1 regime here
is EL1 or EL2. This follows the model body, independently of feature-vector pins. -/
theorem no_a32_regime (p : Prop) [Decidable p] :
    HaveAArch32EL (if p then 2#2 else 1#2) = false := by
  split <;> rfl

theorem address_run (target : BitVec 64) (s : NativeState) (hp : CallerControls s)
    (bit55 : BitVec.access target 55 = 0#1) :
    (AArch64_BranchAddr target 0#2 : SailM (BitVec 64)) s =
      .ok (addressValue target s) (addressState target s) := by
  rw [address_complete target s hp.f4 hp.f2 hp.f3 hp.f6 hp.f7 hp.rme hp.vhe hp.brbe hp.el hp.nrw hp.e2h hp.tge hp.ns hp.pmb hp.spe hp.pmbs hp.nspb hp.nspbe bit55]
  have total : ∃ value t, address_native target s = .ok value t := by
    unfold address_native
    simp only [no_a32_regime, Bool.false_eq_true, false_and, and_false, dif_neg, if_false]
    repeat' first | exact ⟨_, _, rfl⟩ | split
  obtain ⟨value, t, eq⟩ := total
  simp only [addressValue, addressState, eq, nativeResultState, wordResultValue]

theorem spe_run (target : BitVec 64) (branch : BranchType) (conditional : Bool)
    (s : NativeState) (hp : CallerControls s) :
    (SPEBranch target branch conditional true : SailM Unit) s =
      .ok () (speState target branch conditional s) := by
  rw [spe_complete target branch conditional s hp.f4 hp.f2 hp.f3 hp.f6 hp.f7 hp.rme hp.vhe hp.brbe hp.el hp.nrw hp.e2h hp.tge hp.ns hp.pmb hp.spe hp.pmbs hp.nspb hp.nspbe]
  rfl

theorem low_bit55 (target : BitVec 64) (low : target.toNat < 2^55) :
    BitVec.access target 55 = 0#1 := by
  change BitVec.ofBool (target.toNat.testBit 55) = 0#1
  rw [Nat.testBit_lt_two_pow low]
  rfl

theorem low_untag (target : BitVec 64) (low : target.toNat < 2^55) :
    Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb target 55 0) 64 = target := by
  apply BitVec.eq_of_toNat_eq
  have lo56 : target.toNat < 2^56 := Nat.lt_trans low (by decide +kernel)
  simp only [Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, BitVec.zeroExtend_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reduceSub, Nat.reduceAdd]
  rw [Nat.mod_eq_of_lt lo56, Nat.mod_eq_of_lt target.isLt]

#print axioms bl_boundary
#print axioms bl_controls
#print axioms bl_btn
#print axioms bl_PSTATE
#print axioms bl__PC
#print axioms bl_FPCR
#print axioms bl_FPSR
#print axioms bl__Z
#print axioms bl_SP_EL0
#print axioms bl_mem
#print axioms bl_events
#print axioms bl_tags
#print axioms bl_cycleCount
#print axioms bl_sailOutput
#print axioms bl_choiceState
#print axioms blr_boundary
#print axioms blr_controls
#print axioms blr_btn
#print axioms blr_PSTATE
#print axioms blr__PC
#print axioms blr_FPCR
#print axioms blr_FPSR
#print axioms blr__Z
#print axioms blr_SP_EL0
#print axioms blr_mem
#print axioms blr_events
#print axioms blr_tags
#print axioms blr_cycleCount
#print axioms blr_sailOutput
#print axioms blr_choiceState
#print axioms no_a32_regime
#print axioms address_run
#print axioms spe_run
#print axioms low_bit55
#print axioms low_untag
end NativeEntryCallerParts
