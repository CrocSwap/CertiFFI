import ArmCertR14Tails.UbfmLsr1
import ArmCertR14Tails.SubsShift64ZRd
import ArmCertR14Tails.AddShift64
import ArmCertR14Tails.Movz32
import ArmCertR14Tails.OrrShift64
import ArmCertR14Tails.SubsImm32
import ArmCertR14Tails.AddImm32
import ArmCertR14Tails.SubImm32
import ArmCertR14Tails.Movz32Hw1
import ArmCertR14Tails.SubsShift32
import HeapV2StepCerts.RootTailV
import TranslateScalarTagCheck.Actions
import DefaultScalarTrace
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000
namespace ReleaseProfile.DefaultRuntimeScalarChoice
theorem action_UbfmLsr1 (Rd : BitVec 5) (Rn : BitVec 5) :
    TagCheckFrames.Preserves (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 1#6 1#1 2#2 1#1) := by
  unfold decode_ubfm_aarch64_instrs_integer_bitfield execute_aarch64_instrs_integer_bitfield
  scalar_oracle_frame

#print axioms action_UbfmLsr1

theorem tail_UbfmLsr1 (real : Type) [Sail.SailReal real] (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.UbfmLsr1.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.UbfmLsr1.selected Rd Rn) 31 12 == 879088#20) = false) :
    ReleaseProfile.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.UbfmLsr1.selected Rd Rn) := by
  apply ReleaseProfile.DefaultScalarTrace.tail_choice_of_prefix real source (NativeEntryBodyDispatch.UbfmLsr1.selected Rd Rn)
    NativeEntryBodyAdapters.UbfmLsr1.writes 78 (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 1#6 1#1 2#2 1#1) noEret
  · intro state input value after run
    exact action_UbfmLsr1 Rd Rn state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, after, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      ArmCertR14.RootV.UbfmLsr1.action_prefixV real source fetched enc0 Rd Rn rd rn profile
        pins input guard (budget + 1) quiet
    exact ⟨⟨sp, after, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_UbfmLsr1

theorem action_SubsShift64ZRd (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) :
    TagCheckFrames.Preserves (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5 Rn imm6 Rm 0#2 1#1 1#1 1#1) := by
  unfold decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
  scalar_oracle_frame

#print axioms action_SubsShift64ZRd

theorem tail_SubsShift64ZRd (real : Type) [Sail.SailReal real] (source : NativeState)
    (Rn : BitVec 5)
    (imm6 : BitVec 6)
    (Rm : BitVec 5) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsShift64ZRd.selected Rn imm6 Rm) 31 12 == 879088#20) = false) :
    ReleaseProfile.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SubsShift64ZRd.selected Rn imm6 Rm) := by
  apply ReleaseProfile.DefaultScalarTrace.tail_choice_of_prefix real source (NativeEntryBodyDispatch.SubsShift64ZRd.selected Rn imm6 Rm)
    NativeEntryBodyFlag.SubsShift64ZRd.writes 17 (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5 Rn imm6 Rm 0#2 1#1 1#1 1#1) noEret
  · intro state input value after run
    exact action_SubsShift64ZRd Rn imm6 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, after, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, result⟩ :=
      ArmCertR14.RootV.SubsShift64ZRd.action_prefixV real source fetched enc0 Rn imm6 Rm rn rm
        pins input guard (budget + 1) quiet
    exact ⟨⟨sp, after, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_SubsShift64ZRd

theorem action_AddShift64 (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) :
    TagCheckFrames.Preserves (decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 0#1 0#1 1#1) := by
  unfold decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
  scalar_oracle_frame

#print axioms action_AddShift64

theorem tail_AddShift64 (real : Type) [Sail.SailReal real] (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (imm6 : BitVec 6)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (profile : NativeEntryBodyAdapters.AddShift64.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddShift64.selected Rd Rn imm6 Rm) 31 12 == 879088#20) = false) :
    ReleaseProfile.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.AddShift64.selected Rd Rn imm6 Rm) := by
  apply ReleaseProfile.DefaultScalarTrace.tail_choice_of_prefix real source (NativeEntryBodyDispatch.AddShift64.selected Rd Rn imm6 Rm)
    NativeEntryBodyAdapters.AddShift64.writes 14 (decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 0#1 0#1 1#1) noEret
  · intro state input value after run
    exact action_AddShift64 Rd Rn imm6 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, after, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      ArmCertR14.RootV.AddShift64.action_prefixV real source fetched enc0 Rd Rn imm6 Rm rd rn rm profile
        pins input guard (budget + 1) quiet
    exact ⟨⟨sp, after, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_AddShift64

theorem action_Movz32 (Rd : BitVec 5) (imm16 : BitVec 16) :
    TagCheckFrames.Preserves (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 0#2 2#2 0#1) := by
  unfold decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide execute_aarch64_instrs_integer_ins_ext_insert_movewide
  scalar_oracle_frame

#print axioms action_Movz32

theorem tail_Movz32 (real : Type) [Sail.SailReal real] (source : NativeState)
    (Rd : BitVec 5)
    (imm16 : BitVec 16) (rd : Rd.toNat < 31)
    (profile : NativeEntryBodyAdapters.Movz32.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Movz32.selected Rd imm16) 31 12 == 879088#20) = false) :
    ReleaseProfile.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Movz32.selected Rd imm16) := by
  apply ReleaseProfile.DefaultScalarTrace.tail_choice_of_prefix real source (NativeEntryBodyDispatch.Movz32.selected Rd imm16)
    NativeEntryBodyAdapters.Movz32.writes 698 (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 0#2 2#2 0#1) noEret
  · intro state input value after run
    exact action_Movz32 Rd imm16 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, after, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      ArmCertR14.RootV.Movz32.action_prefixV real source fetched enc0 Rd imm16 rd profile
        pins input guard (budget + 1) quiet
    exact ⟨⟨sp, after, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_Movz32

theorem action_OrrShift64 (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) :
    TagCheckFrames.Preserves (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm 0#1 0#2 1#2 1#1) := by
  unfold decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg execute_aarch64_instrs_integer_logical_shiftedreg
  scalar_oracle_frame

#print axioms action_OrrShift64

theorem tail_OrrShift64 (real : Type) [Sail.SailReal real] (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (imm6 : BitVec 6)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (profile : NativeEntryBodyAdapters.OrrShift64.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.OrrShift64.selected Rd Rn imm6 Rm) 31 12 == 879088#20) = false) :
    ReleaseProfile.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.OrrShift64.selected Rd Rn imm6 Rm) := by
  apply ReleaseProfile.DefaultScalarTrace.tail_choice_of_prefix real source (NativeEntryBodyDispatch.OrrShift64.selected Rd Rn imm6 Rm)
    NativeEntryBodyAdapters.OrrShift64.writes 55 (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm 0#1 0#2 1#2 1#1) noEret
  · intro state input value after run
    exact action_OrrShift64 Rd Rn imm6 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, after, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      ArmCertR14.RootV.OrrShift64.action_prefixV real source fetched enc0 Rd Rn imm6 Rm rd rn rm profile
        pins input guard (budget + 1) quiet
    exact ⟨⟨sp, after, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_OrrShift64

theorem action_SubsImm32 (Rn : BitVec 5) (imm12 : BitVec 12) :
    TagCheckFrames.Preserves (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 0#1) := by
  unfold decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
  scalar_oracle_frame

#print axioms action_SubsImm32

theorem tail_SubsImm32 (real : Type) [Sail.SailReal real] (source : NativeState)
    (Rn : BitVec 5)
    (imm12 : BitVec 12) (rn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.selected Rn imm12) 31 12 == 879088#20) = false) :
    ReleaseProfile.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SubsImm32.selected Rn imm12) := by
  apply ReleaseProfile.DefaultScalarTrace.tail_choice_of_prefix real source (NativeEntryBodyDispatch.SubsImm32.selected Rn imm12)
    NativeEntryBodyFlag.SubsImm32.writes 21 (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 0#1) noEret
  · intro state input value after run
    exact action_SubsImm32 Rn imm12 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, after, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, result⟩ :=
      ArmCertR14.RootV.SubsImm32.action_prefixV real source fetched enc0 Rn imm12 rn
        pins input guard (budget + 1) quiet
    exact ⟨⟨sp, after, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_SubsImm32

theorem action_AddImm32 (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) :
    TagCheckFrames.Preserves (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 0#1 0#1) := by
  unfold decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
  scalar_oracle_frame

#print axioms action_AddImm32

theorem tail_AddImm32 (real : Type) [Sail.SailReal real] (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.AddImm32.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) 31 12 == 879088#20) = false) :
    ReleaseProfile.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) := by
  apply ReleaseProfile.DefaultScalarTrace.tail_choice_of_prefix real source (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12)
    NativeEntryBodyAdapters.AddImm32.writes 18 (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 0#1 0#1) noEret
  · intro state input value after run
    exact action_AddImm32 Rd Rn imm12 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, after, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      ArmCertR14.RootV.AddImm32.action_prefixV real source fetched enc0 Rd Rn imm12 rd rn profile
        pins input guard (budget + 1) quiet
    exact ⟨⟨sp, after, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_AddImm32

theorem action_SubImm32 (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) :
    TagCheckFrames.Preserves (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 1#1 0#1) := by
  unfold decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
  scalar_oracle_frame

#print axioms action_SubImm32

theorem tail_SubImm32 (real : Type) [Sail.SailReal real] (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.SubImm32.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubImm32.selected Rd Rn imm12) 31 12 == 879088#20) = false) :
    ReleaseProfile.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SubImm32.selected Rd Rn imm12) := by
  apply ReleaseProfile.DefaultScalarTrace.tail_choice_of_prefix real source (NativeEntryBodyDispatch.SubImm32.selected Rd Rn imm12)
    NativeEntryBodyAdapters.SubImm32.writes 20 (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 1#1 0#1) noEret
  · intro state input value after run
    exact action_SubImm32 Rd Rn imm12 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, after, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      ArmCertR14.RootV.SubImm32.action_prefixV real source fetched enc0 Rd Rn imm12 rd rn profile
        pins input guard (budget + 1) quiet
    exact ⟨⟨sp, after, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_SubImm32

theorem action_Movz32Hw1 (Rd : BitVec 5) (imm16 : BitVec 16) :
    TagCheckFrames.Preserves (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 1#2 2#2 0#1) := by
  unfold decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide execute_aarch64_instrs_integer_ins_ext_insert_movewide
  scalar_oracle_frame

#print axioms action_Movz32Hw1

theorem tail_Movz32Hw1 (real : Type) [Sail.SailReal real] (source : NativeState)
    (Rd : BitVec 5)
    (imm16 : BitVec 16) (rd : Rd.toNat < 31)
    (profile : NativeEntryBodyAdapters.Movz32Hw1.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) 31 12 == 879088#20) = false) :
    ReleaseProfile.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) := by
  apply ReleaseProfile.DefaultScalarTrace.tail_choice_of_prefix real source (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16)
    NativeEntryBodyAdapters.Movz32Hw1.writes 698 (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 1#2 2#2 0#1) noEret
  · intro state input value after run
    exact action_Movz32Hw1 Rd imm16 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, after, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      ArmCertR14.RootV.Movz32Hw1.action_prefixV real source fetched enc0 Rd imm16 rd profile
        pins input guard (budget + 1) quiet
    exact ⟨⟨sp, after, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_Movz32Hw1

theorem action_SubsShift32 (Rn : BitVec 5) (Rm : BitVec 5) :
    TagCheckFrames.Preserves (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5 Rn 0#6 Rm 0#2 1#1 1#1 0#1) := by
  unfold decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
  scalar_oracle_frame

#print axioms action_SubsShift32

theorem tail_SubsShift32 (real : Type) [Sail.SailReal real] (source : NativeState)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsShift32.selected Rn Rm) 31 12 == 879088#20) = false) :
    ReleaseProfile.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SubsShift32.selected Rn Rm) := by
  apply ReleaseProfile.DefaultScalarTrace.tail_choice_of_prefix real source (NativeEntryBodyDispatch.SubsShift32.selected Rn Rm)
    NativeEntryBodyFlag.SubsShift32.writes 17 (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5 Rn 0#6 Rm 0#2 1#1 1#1 0#1) noEret
  · intro state input value after run
    exact action_SubsShift32 Rn Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, after, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, result⟩ :=
      ArmCertR14.RootV.SubsShift32.action_prefixV real source fetched enc0 Rn Rm rn rm
        pins input guard (budget + 1) quiet
    exact ⟨⟨sp, after, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_SubsShift32

theorem tail_OrrMov64 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (imm6 : BitVec 6)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rm : Rm.toNat < 31) (h6 : imm6 = 0#6)
    (profile : NativeEntryBodyAdapters.OrrMov64.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.OrrMov64.selected Rd imm6 Rm) 31 12 == 879088#20) = false) :
    ReleaseProfile.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.OrrMov64.selected Rd imm6 Rm) := by
  apply ReleaseProfile.DefaultScalarTrace.tail_choice_of_prefix real source (NativeEntryBodyDispatch.OrrMov64.selected Rd imm6 Rm)
    NativeEntryBodyAdapters.OrrMov64.writes 55 (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd 31#5 imm6 Rm 0#1 0#2 1#2 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_19 Rd 31#5 imm6 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.OrrMov64.action_prefixV real source fetched enc0 Rd imm6 Rm rd rm h6 profile pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_OrrMov64

theorem tail_AddSp (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (imm12 : BitVec 12) (rd : Rd.toNat < 31)
    (profile : NativeEntryBodyAdapters.AddSp.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddSp.selected Rd imm12) 31 12 == 879088#20) = false) :
    ReleaseProfile.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.AddSp.selected Rd imm12) := by
  apply ReleaseProfile.DefaultScalarTrace.tail_choice_of_prefix real source (NativeEntryBodyDispatch.AddSp.selected Rd imm12)
    NativeEntryBodyAdapters.AddSp.writes 18 (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd 31#5 imm12 0#1 0#1 0#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_2 Rd 31#5 imm12 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.AddSp.action_prefixV real source fetched enc0 Rd imm12 rd profile pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_AddSp

end ReleaseProfile.DefaultRuntimeScalarChoice
