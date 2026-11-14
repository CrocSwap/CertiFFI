import ArmCertR14Tails.Sbcs64Reg
import HeapV2StepCerts.FlagRootV
import HeapV2StepCerts.RootTailV
import TranslateScalarTagCheck.Actions
import TranslateSpan.DefaultScalarTrace
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option Elab.async false
namespace TranslateScalarTagCheck.Tails
theorem tail_0 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
   
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Sbcs64Reg.selected Rd Rn Rm) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Sbcs64Reg.selected Rd Rn Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.Sbcs64Reg.selected Rd Rn Rm)
    NativeEntryBodyFlag.Sbcs64Reg.writes 9 (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 1#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_22 Rd Rn Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      ArmCertR14.RootV.Sbcs64Reg.action_prefixV real source fetched enc0 Rd Rn Rm rd rn rm pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_0

theorem tail_1 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.AddImm64.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddImm64.selected Rd Rn imm12) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.AddImm64.selected Rd Rn imm12) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.AddImm64.selected Rd Rn imm12)
    NativeEntryBodyAdapters.AddImm64.writes 18 (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 0#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_2 Rd Rn imm12 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.AddImm64.action_prefixV real source fetched enc0 Rd Rn imm12 rd rn profile pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_1

theorem tail_2 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (imm16 : BitVec 16) (rd : Rd.toNat < 31)
    (profile : NativeEntryBodyAdapters.Movz64z.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Movz64z.selected Rd imm16) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Movz64z.selected Rd imm16) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.Movz64z.selected Rd imm16)
    NativeEntryBodyAdapters.Movz64z.writes 698 (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 0#2 2#2 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_17 Rd imm16 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.Movz64z.action_prefixV real source fetched enc0 Rd imm16 rd profile pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_2

theorem tail_3 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (profile : NativeEntryBodyAdapters.Madd64.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Madd64.selected Rd Rn Rm) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Madd64.selected Rd Rn Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.Madd64.selected Rd Rn Rm)
    NativeEntryBodyAdapters.Madd64.writes 690 (decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub Rd Rn 31#5 0#1 Rm 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_16 Rd Rn 31#5 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.Madd64.action_prefixV real source fetched enc0 Rd Rn Rm rd rn rm profile pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_3

theorem tail_4 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (profile : NativeEntryBodyAdapters.Umulh64.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Umulh64.selected Rd Rn Rm) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Umulh64.selected Rd Rn Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.Umulh64.selected Rd Rn Rm)
    NativeEntryBodyAdapters.Umulh64.writes 862 (decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_26 Rd Rn 31#5 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.Umulh64.action_prefixV real source fetched enc0 Rd Rn Rm rd rn rm profile pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_4

theorem tail_5 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (profile : NativeEntryBodyAdapters.Adc64.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.selected Rd Rn Rm) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Adc64.selected Rd Rn Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.Adc64.selected Rd Rn Rm)
    NativeEntryBodyAdapters.Adc64.writes 6 (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 0#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_0 Rd Rn Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.Adc64.action_prefixV real source fetched enc0 Rd Rn Rm rd rn rm profile pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_5

theorem tail_6 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.Adc64ZRm.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64ZRm.selected Rd Rn) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Adc64ZRm.selected Rd Rn) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.Adc64ZRm.selected Rd Rn)
    NativeEntryBodyAdapters.Adc64ZRm.writes 6 (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 0#1 0#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_0 Rd Rn 31#5 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.Adc64ZRm.action_prefixV real source fetched enc0 Rd Rn rd rn profile pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_6

theorem tail_7 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.Sbc64.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Sbc64.selected Rd Rn) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Sbc64.selected Rd Rn) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.Sbc64.selected Rd Rn)
    NativeEntryBodyAdapters.Sbc64.writes 8 (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 0#1 1#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_21 Rd Rn 31#5 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.Sbc64.action_prefixV real source fetched enc0 Rd Rn rd rn profile pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_7

theorem tail_8 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.OrrImm32_0.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn)
    NativeEntryBodyAdapters.OrrImm32_0.writes 43 (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn 0#6 32#6 1#1 1#2 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_18 Rd Rn 0#6 32#6 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.OrrImm32_0.action_prefixV real source fetched enc0 Rd Rn rd rn profile pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_8

theorem tail_9 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (imm6 : BitVec 6)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rm : Rm.toNat < 31) (h6 : imm6 = 0#6)
    (profile : NativeEntryBodyAdapters.OrrMov64.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.OrrMov64.selected Rd imm6 Rm) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.OrrMov64.selected Rd imm6 Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.OrrMov64.selected Rd imm6 Rm)
    NativeEntryBodyAdapters.OrrMov64.writes 55 (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd 31#5 imm6 Rm 0#1 0#2 1#2 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_19 Rd 31#5 imm6 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.OrrMov64.action_prefixV real source fetched enc0 Rd imm6 Rm rd rm h6 profile pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_9

theorem tail_10 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (imm12 : BitVec 12) (rd : Rd.toNat < 31)
    (profile : NativeEntryBodyAdapters.AddSp.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddSp.selected Rd imm12) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.AddSp.selected Rd imm12) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.AddSp.selected Rd imm12)
    NativeEntryBodyAdapters.AddSp.writes 18 (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd 31#5 imm12 0#1 0#1 0#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_2 Rd 31#5 imm12 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.AddSp.action_prefixV real source fetched enc0 Rd imm12 rd profile pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_10

theorem tail_11 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (imm12 : BitVec 12)
    (profile : NativeEntryBodyAdapters.AddSpRestore.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddSpRestore.selected imm12) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.AddSpRestore.selected imm12) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.AddSpRestore.selected imm12)
    NativeEntryBodyAdapters.AddSpRestore.writes 18 (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 31#5 imm12 0#1 0#1 0#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_2 31#5 31#5 imm12 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.AddSpRestore.action_prefixV real source fetched enc0 imm12 profile pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_11

theorem tail_12 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
   
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adcs64.selected Rd Rn Rm) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Adcs64.selected Rd Rn Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.Adcs64.selected Rd Rn Rm)
    NativeEntryBodyFlag.Adcs64.writes 7 (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_1 Rd Rn Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.Adcs64.action_prefixV real source fetched enc0 Rd Rn Rm rd rn rm pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_12

theorem tail_13 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
   
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn)
    NativeEntryBodyFlag.Adcs64ZRm.writes 7 (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 0#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_1 Rd Rn 31#5 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.Adcs64ZRm.action_prefixV real source fetched enc0 Rd Rn rd rn pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_13

theorem tail_14 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (imm6 : BitVec 6)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
   
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddsShift64.selected Rd Rn imm6 Rm) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.AddsShift64.selected Rd Rn imm6 Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.AddsShift64.selected Rd Rn imm6 Rm)
    NativeEntryBodyFlag.AddsShift64.writes 15 (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 1#1 0#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_4 Rd Rn imm6 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.AddsShift64.action_prefixV real source fetched enc0 Rd Rn imm6 Rm rd rn rm pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_14

theorem tail_15 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (imm6 : BitVec 6)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
   
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm)
    NativeEntryBodyFlag.SubsShift64.writes 17 (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 1#1 1#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_23 Rd Rn imm6 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.SubsShift64.action_prefixV real source fetched enc0 Rd Rn imm6 Rm rd rn rm pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_15

theorem tail_16 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
   
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Csel3.selected Rd Rn) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Csel3.selected Rd Rn) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.Csel3.selected Rd Rn)
    NativeEntryBodyFlag.Csel3.writes 187 (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 31#5 0#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_9 Rd Rn 31#5 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.FlagV.Csel3.action_prefixV real source fetched enc0 Rd Rn rd rn pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_16

theorem tail_17 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5) (rd : Rd.toNat < 31)
   
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Csinc3.selected Rd) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Csinc3.selected Rd) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.Csinc3.selected Rd)
    NativeEntryBodyFlag.Csinc3.writes 188 (decode_csinc_aarch64_instrs_integer_conditional_select Rd 31#5 1#1 3#4 31#5 0#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_10 Rd 31#5 31#5 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.FlagV.Csinc3.action_prefixV real source fetched enc0 Rd rd pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_17

theorem tail_18 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
   
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Sbcs64.selected Rd Rn) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Sbcs64.selected Rd Rn) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.Sbcs64.selected Rd Rn)
    NativeEntryBodyFlag.Sbcs64.writes 9 (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 1#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_22 Rd Rn 31#5 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.FlagV.Sbcs64.action_prefixV real source fetched enc0 Rd Rn rd rn pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_18

theorem tail_19 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
   
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Subsi64.selected Rd Rn imm12) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Subsi64.selected Rd Rn imm12) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.Subsi64.selected Rd Rn imm12)
    NativeEntryBodyFlag.Subsi64.writes 21 (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_31 Rd Rn imm12 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.Subsi64.action_prefixV real source fetched enc0 Rd Rn imm12 rd rn pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_19

theorem tail_20 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rn : BitVec 5)
    (imm12 : BitVec 12) (rn : Rn.toNat < 31)
   
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Subsi64ZRd.selected Rn imm12) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.Subsi64ZRd.selected Rn imm12) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.Subsi64ZRd.selected Rn imm12)
    NativeEntryBodyFlag.Subsi64ZRd.writes 21 (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_28 Rn imm12 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.Subsi64ZRd.action_prefixV real source fetched enc0 Rn imm12 rn pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_20

theorem tail_21 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rn : BitVec 5) (rn : Rn.toNat < 31)
   
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.AndsImm0_2.selected Rn)
    NativeEntryBodyFlag.AndsImm0_2.writes 41 (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_32 31#5 Rn 2#6 0#6 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.AndsImm0_2.action_prefixV real source fetched enc0 Rn rn pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_21

theorem tail_22 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (imm12 : BitVec 12)
    (profile : NativeEntryBodyAdapters.SubSp64.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubSp64.selected imm12) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SubSp64.selected imm12) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SubSp64.selected imm12)
    NativeEntryBodyAdapters.SubSp64.writes 20 (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 31#5 imm12 0#1 0#1 1#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_33 31#5 31#5 imm12 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, a, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, result⟩ :=
      HeapV2StepCerts.RootV.SubSp64.action_prefixV real source fetched enc0 imm12 profile pins input guard (budget + 1) quiet
    exact ⟨⟨sp, a, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

#print axioms tail_22

end TranslateScalarTagCheck.Tails
