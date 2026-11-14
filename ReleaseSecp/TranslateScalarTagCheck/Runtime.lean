import N1D226.AdcZeroRn64Generic.Progress
import N1D226.AddsShift64Generic.Progress
import N1D226.BicRuntime.Progress
import N1D226.CmnImm64Generic.Progress
import N1D226.CmpShiftZero64.Progress
import N1D226.CmpZero64.Progress
import N1D226.CselCc64Generic.Progress
import N1D226.CsetEq32.Progress
import N1D226.CsinvCs64Generic.Progress
import N1D226.CsnegCs64Generic.Progress
import N1D226.Extr64Generic.Progress
import N1D226.Madd64Generic.Progress
import N1D226.OrnZeroBorrow.Progress
import N1D226.SubShiftBorrow.Progress
import N1D226.Umaddl64Generic.Progress
import TranslateScalarTagCheck.Actions
import TranslateSpan.DefaultScalarTrace
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model ArmCertWalk ArmCertValue
open TranslateSpan NativeMteTagCheck
open HeapV2StepCerts.RegBind (rk)
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option Elab.async false
namespace TranslateScalarTagCheck.Runtime
theorem tail_0 (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (N1D226.BicRuntime.Encoding.selected Rd Rn imm6 Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (N1D226.BicRuntime.Encoding.selected Rd Rn imm6 Rm)
    {} 50 (decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm 1#1 0#2 0#2 1#1) (N1D226.BicRuntime.Tail.noEret Rd Rn imm6 Rm)
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_7 Rd Rn imm6 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, act, hook, metadataInput, _, frame, actionQuiet, action, boundary, _, _⟩ :=
      N1D226.BicRuntime.Progress.action_prefix real source fetched enc0 Rd Rn imm6 Rm rd rn rm
        pins input guard (budget + 1) quiet
    refine ⟨⟨sp, act, hook, metadataInput, boundary, frame, actionQuiet, ?_⟩⟩
    rw [action]
    rfl

#print axioms tail_0

theorem outputs_0 (real : Type) [Sail.SailReal real]
    (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (profile : NativeAccess.AccessProfile) (catalogue : ControlCatalogue) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0)
    (aligned : (offset k).toNat % 4 = 0) (view : Physical.BytePA) (regions : List Region) (source fin : NativeState)
    (core : DefaultMTE2.Core spec config rows mapping consumer scope image loadBase
      base offset budget profile catalogue k source)
    (ob : FetchObligations spec config rows mapping (N1D226.BicRuntime.Encoding.selected Rd Rn imm6 Rm) source)
    (stepRun : modelStep real source = .ok () fin) :
    Expr.OutputHolds [(.reg (.x (rk Rd)), N1D226.BicRuntime.ExprValue.term Rd Rn imm6 Rm)] source fin := by
  apply TranslateSpan.DefaultScalarTrace.outputs_of_step real spec config rows mapping consumer scope
    image loadBase base offset budget profile catalogue k room page aligned (N1D226.BicRuntime.Encoding.selected Rd Rn imm6 Rm)
    source fin core ob [(.reg (.x (rk Rd)), N1D226.BicRuntime.ExprValue.term Rd Rn imm6 Rm)] ?_ stepRun
  intro fetched enc0 ticks pins input guard quiet it ss run
  exact (N1D226.BicRuntime.Progress.g_holds_of_native real source fetched enc0 Rd Rn imm6 Rm rd rn rm
    pins input guard ticks quiet it ss view regions fin run).1

#print axioms outputs_0

theorem tail_1 (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rn : BitVec 5) (imm12 : BitVec 12) (rn : Rn.toNat < 31) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (N1D226.CmpZero64.Encoding.selected Rn imm12) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (N1D226.CmpZero64.Encoding.selected Rn imm12)
    {} 21 (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 1#1) (N1D226.CmpZero64.Tail.noEret Rn imm12)
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_28 Rn imm12 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, act, hook, metadataInput, _, frame, actionQuiet, action, boundary, _, _⟩ :=
      N1D226.CmpZero64.Progress.action_prefix real source fetched enc0 Rn imm12 rn
        pins input guard (budget + 1) quiet
    refine ⟨⟨sp, act, hook, metadataInput, boundary, frame, actionQuiet, ?_⟩⟩
    rw [action]
    rfl

#print axioms tail_1

theorem tail_2 (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rd : BitVec 5) (rd : Rd.toNat < 31) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (N1D226.CsetEq32.Encoding.selected Rd) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (N1D226.CsetEq32.Encoding.selected Rd)
    {} 188 (decode_csinc_aarch64_instrs_integer_conditional_select Rd 31#5 1#1 1#4 31#5 0#1 0#1) (N1D226.CsetEq32.Tail.noEret Rd)
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_27 Rd state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, act, hook, metadataInput, _, frame, actionQuiet, action, boundary, _, _⟩ :=
      N1D226.CsetEq32.Progress.action_prefix real source fetched enc0 Rd rd
        pins input guard (budget + 1) quiet
    refine ⟨⟨sp, act, hook, metadataInput, boundary, frame, actionQuiet, ?_⟩⟩
    rw [action]
    rfl

#print axioms tail_2

theorem tail_3 (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm)
    {} 54 (decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm 1#1 0#2 1#2 1#1) (N1D226.OrnZeroBorrow.Tail.noEret Rd Rn imm6 Rm)
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_34 Rd Rn imm6 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, act, hook, metadataInput, _, frame, actionQuiet, action, boundary, _, _⟩ :=
      N1D226.OrnZeroBorrow.Progress.action_prefix real source fetched enc0 Rd Rn imm6 Rm rd rn rm
        pins input guard (budget + 1) quiet
    refine ⟨⟨sp, act, hook, metadataInput, boundary, frame, actionQuiet, ?_⟩⟩
    rw [action]
    rfl

#print axioms tail_3

theorem outputs_3 (real : Type) [Sail.SailReal real]
    (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (profile : NativeAccess.AccessProfile) (catalogue : ControlCatalogue) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0)
    (aligned : (offset k).toNat % 4 = 0) (view : Physical.BytePA) (regions : List Region) (source fin : NativeState)
    (core : DefaultMTE2.Core spec config rows mapping consumer scope image loadBase
      base offset budget profile catalogue k source)
    (ob : FetchObligations spec config rows mapping (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) source)
    (stepRun : modelStep real source = .ok () fin) :
    Expr.OutputHolds [(.reg (.x (rk Rd)), N1D226.OrnZeroBorrow.ExprValue.term Rd Rn imm6 Rm)] source fin := by
  apply TranslateSpan.DefaultScalarTrace.outputs_of_step real spec config rows mapping consumer scope
    image loadBase base offset budget profile catalogue k room page aligned (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm)
    source fin core ob [(.reg (.x (rk Rd)), N1D226.OrnZeroBorrow.ExprValue.term Rd Rn imm6 Rm)] ?_ stepRun
  intro fetched enc0 ticks pins input guard quiet it ss run
  exact (N1D226.OrnZeroBorrow.Progress.g_holds_of_native real source fetched enc0 Rd Rn imm6 Rm rd rn rm
    pins input guard ticks quiet it ss view regions fin run).1

#print axioms outputs_3

theorem tail_4 (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm)
    {} 16 (decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 0#1 1#1 1#1) (N1D226.SubShiftBorrow.Tail.noEret Rd Rn imm6 Rm)
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_35 Rd Rn imm6 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, act, hook, metadataInput, _, frame, actionQuiet, action, boundary, _, _⟩ :=
      N1D226.SubShiftBorrow.Progress.action_prefix real source fetched enc0 Rd Rn imm6 Rm rd rn rm
        pins input guard (budget + 1) quiet
    refine ⟨⟨sp, act, hook, metadataInput, boundary, frame, actionQuiet, ?_⟩⟩
    rw [action]
    rfl

#print axioms tail_4

theorem outputs_4 (real : Type) [Sail.SailReal real]
    (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (profile : NativeAccess.AccessProfile) (catalogue : ControlCatalogue) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0)
    (aligned : (offset k).toNat % 4 = 0) (view : Physical.BytePA) (regions : List Region) (source fin : NativeState)
    (core : DefaultMTE2.Core spec config rows mapping consumer scope image loadBase
      base offset budget profile catalogue k source)
    (ob : FetchObligations spec config rows mapping (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) source)
    (stepRun : modelStep real source = .ok () fin) :
    Expr.OutputHolds [(.reg (.x (rk Rd)), N1D226.SubShiftBorrow.ExprValue.term Rd Rn imm6 Rm)] source fin := by
  apply TranslateSpan.DefaultScalarTrace.outputs_of_step real spec config rows mapping consumer scope
    image loadBase base offset budget profile catalogue k room page aligned (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm)
    source fin core ob [(.reg (.x (rk Rd)), N1D226.SubShiftBorrow.ExprValue.term Rd Rn imm6 Rm)] ?_ stepRun
  intro fetched enc0 ticks pins input guard quiet it ss run
  exact (N1D226.SubShiftBorrow.Progress.g_holds_of_native real source fetched enc0 Rd Rn imm6 Rm rd rn rm
    pins input guard ticks quiet it ss view regions fin run).1

#print axioms outputs_4

theorem tail_5 (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Ra : BitVec 5) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (ra : Ra.toNat < 31) (rm : Rm.toNat < 31) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (N1D226.Madd64Generic.Encoding.selected Rd Rn Ra Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (N1D226.Madd64Generic.Encoding.selected Rd Rn Ra Rm)
    {} 690 (decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub Rd Rn Ra 0#1 Rm 1#1) (N1D226.Madd64Generic.Tail.noEret Rd Rn Ra Rm)
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_16 Rd Rn Ra Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, act, hook, metadataInput, _, frame, actionQuiet, action, boundary, _, _⟩ :=
      N1D226.Madd64Generic.Progress.action_prefix real source fetched enc0 Rd Rn Ra Rm rd rn ra rm
        pins input guard (budget + 1) quiet
    refine ⟨⟨sp, act, hook, metadataInput, boundary, frame, actionQuiet, ?_⟩⟩
    rw [action]
    rfl

#print axioms tail_5

theorem outputs_5 (real : Type) [Sail.SailReal real]
    (Rd : BitVec 5) (Rn : BitVec 5) (Ra : BitVec 5) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (ra : Ra.toNat < 31) (rm : Rm.toNat < 31)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (profile : NativeAccess.AccessProfile) (catalogue : ControlCatalogue) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0)
    (aligned : (offset k).toNat % 4 = 0) (view : Physical.BytePA) (regions : List Region) (source fin : NativeState)
    (core : DefaultMTE2.Core spec config rows mapping consumer scope image loadBase
      base offset budget profile catalogue k source)
    (ob : FetchObligations spec config rows mapping (N1D226.Madd64Generic.Encoding.selected Rd Rn Ra Rm) source)
    (stepRun : modelStep real source = .ok () fin) :
    Expr.OutputHolds [(.reg (.x (rk Rd)), N1D226.Madd64Generic.ExprValue.term Rn Ra Rm)] source fin := by
  apply TranslateSpan.DefaultScalarTrace.outputs_of_step real spec config rows mapping consumer scope
    image loadBase base offset budget profile catalogue k room page aligned (N1D226.Madd64Generic.Encoding.selected Rd Rn Ra Rm)
    source fin core ob [(.reg (.x (rk Rd)), N1D226.Madd64Generic.ExprValue.term Rn Ra Rm)] ?_ stepRun
  intro fetched enc0 ticks pins input guard quiet it ss run
  exact (N1D226.Madd64Generic.Progress.g_holds_of_native real source fetched enc0 Rd Rn Ra Rm rd rn ra rm
    pins input guard ticks quiet it ss view regions fin run).1

#print axioms outputs_5

theorem tail_6 (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (N1D226.Umaddl64Generic.Encoding.selected Rd Rn Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (N1D226.Umaddl64Generic.Encoding.selected Rd Rn Rm)
    {} 830 (decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn 31#5 0#1 Rm 1#1) (N1D226.Umaddl64Generic.Tail.noEret Rd Rn Rm)
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_25 Rd Rn 31#5 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, act, hook, metadataInput, _, frame, actionQuiet, action, boundary, _, _⟩ :=
      N1D226.Umaddl64Generic.Progress.action_prefix real source fetched enc0 Rd Rn Rm rd rn rm
        pins input guard (budget + 1) quiet
    refine ⟨⟨sp, act, hook, metadataInput, boundary, frame, actionQuiet, ?_⟩⟩
    rw [action]
    rfl

#print axioms tail_6

theorem outputs_6 (real : Type) [Sail.SailReal real]
    (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (profile : NativeAccess.AccessProfile) (catalogue : ControlCatalogue) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0)
    (aligned : (offset k).toNat % 4 = 0) (view : Physical.BytePA) (regions : List Region) (source fin : NativeState)
    (core : DefaultMTE2.Core spec config rows mapping consumer scope image loadBase
      base offset budget profile catalogue k source)
    (ob : FetchObligations spec config rows mapping (N1D226.Umaddl64Generic.Encoding.selected Rd Rn Rm) source)
    (stepRun : modelStep real source = .ok () fin) :
    Expr.OutputHolds [(.reg (.x (rk Rd)), N1D226.Umaddl64Generic.ExprValue.term Rn Rm)] source fin := by
  apply TranslateSpan.DefaultScalarTrace.outputs_of_step real spec config rows mapping consumer scope
    image loadBase base offset budget profile catalogue k room page aligned (N1D226.Umaddl64Generic.Encoding.selected Rd Rn Rm)
    source fin core ob [(.reg (.x (rk Rd)), N1D226.Umaddl64Generic.ExprValue.term Rn Rm)] ?_ stepRun
  intro fetched enc0 ticks pins input guard quiet it ss run
  exact (N1D226.Umaddl64Generic.Progress.g_holds_of_native real source fetched enc0 Rd Rn Rm rd rn rm
    pins input guard ticks quiet it ss view regions fin run).1

#print axioms outputs_6

theorem tail_7 (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rn : BitVec 5) (imm6 : BitVec 6) (rn : Rn.toNat < 31) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (N1D226.CmpShiftZero64.Encoding.selected Rn imm6) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (N1D226.CmpShiftZero64.Encoding.selected Rn imm6)
    {} 17 (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5 Rn imm6 31#5 0#2 1#1 1#1 1#1) (N1D226.CmpShiftZero64.Tail.noEret Rn imm6)
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_23 31#5 Rn imm6 31#5 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, act, hook, metadataInput, _, frame, actionQuiet, action, boundary, _, _⟩ :=
      N1D226.CmpShiftZero64.Progress.action_prefix real source fetched enc0 Rn imm6 rn
        pins input guard (budget + 1) quiet
    refine ⟨⟨sp, act, hook, metadataInput, boundary, frame, actionQuiet, ?_⟩⟩
    rw [action]
    rfl

#print axioms tail_7

theorem tail_8 (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (N1D226.AddsShift64Generic.Encoding.selected Rd Rn imm6 Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (N1D226.AddsShift64Generic.Encoding.selected Rd Rn imm6 Rm)
    {} 15 (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 1#1 0#1 1#1) (N1D226.AddsShift64Generic.Tail.noEret Rd Rn imm6 Rm)
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_4 Rd Rn imm6 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, act, hook, metadataInput, _, frame, actionQuiet, action, boundary, _, _⟩ :=
      N1D226.AddsShift64Generic.Progress.action_prefix real source fetched enc0 Rd Rn imm6 Rm rd rn rm
        pins input guard (budget + 1) quiet
    refine ⟨⟨sp, act, hook, metadataInput, boundary, frame, actionQuiet, ?_⟩⟩
    rw [action]
    rfl

#print axioms tail_8

theorem tail_9 (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (N1D226.CselCc64Generic.Encoding.selected Rd Rn Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (N1D226.CselCc64Generic.Encoding.selected Rd Rn Rm)
    {} 187 (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 Rm 0#1 1#1) (N1D226.CselCc64Generic.Tail.noEret Rd Rn Rm)
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_9 Rd Rn Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, act, hook, metadataInput, _, frame, actionQuiet, action, boundary, _, _⟩ :=
      N1D226.CselCc64Generic.Progress.action_prefix real source fetched enc0 Rd Rn Rm rd rn rm
        pins input guard (budget + 1) quiet
    refine ⟨⟨sp, act, hook, metadataInput, boundary, frame, actionQuiet, ?_⟩⟩
    rw [action]
    rfl

#print axioms tail_9

theorem tail_10 (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rn : BitVec 5) (imm12 : BitVec 12) (rn : Rn.toNat < 31) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (N1D226.CmnImm64Generic.Encoding.selected Rn imm12) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (N1D226.CmnImm64Generic.Encoding.selected Rn imm12)
    {} 19 (decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 0#1 1#1) (N1D226.CmnImm64Generic.Tail.noEret Rn imm12)
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_3 31#5 Rn imm12 state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, act, hook, metadataInput, _, frame, actionQuiet, action, boundary, _, _⟩ :=
      N1D226.CmnImm64Generic.Progress.action_prefix real source fetched enc0 Rn imm12 rn
        pins input guard (budget + 1) quiet
    refine ⟨⟨sp, act, hook, metadataInput, boundary, frame, actionQuiet, ?_⟩⟩
    rw [action]
    rfl

#print axioms tail_10

theorem tail_11 (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (N1D226.CsinvCs64Generic.Encoding.selected Rd Rn Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (N1D226.CsinvCs64Generic.Encoding.selected Rd Rn Rm)
    {} 189 (decode_csinv_aarch64_instrs_integer_conditional_select Rd Rn 0#1 2#4 Rm 1#1 1#1) (N1D226.CsinvCs64Generic.Tail.noEret Rd Rn Rm)
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_12 Rd Rn Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, act, hook, metadataInput, _, frame, actionQuiet, action, boundary, _, _⟩ :=
      N1D226.CsinvCs64Generic.Progress.action_prefix real source fetched enc0 Rd Rn Rm rd rn rm
        pins input guard (budget + 1) quiet
    refine ⟨⟨sp, act, hook, metadataInput, boundary, frame, actionQuiet, ?_⟩⟩
    rw [action]
    rfl

#print axioms tail_11

theorem tail_12 (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (N1D226.CsnegCs64Generic.Encoding.selected Rd Rn Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (N1D226.CsnegCs64Generic.Encoding.selected Rd Rn Rm)
    {} 190 (decode_csneg_aarch64_instrs_integer_conditional_select Rd Rn 1#1 2#4 Rm 1#1 1#1) (N1D226.CsnegCs64Generic.Tail.noEret Rd Rn Rm)
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_13 Rd Rn Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, act, hook, metadataInput, _, frame, actionQuiet, action, boundary, _, _⟩ :=
      N1D226.CsnegCs64Generic.Progress.action_prefix real source fetched enc0 Rd Rn Rm rd rn rm
        pins input guard (budget + 1) quiet
    refine ⟨⟨sp, act, hook, metadataInput, boundary, frame, actionQuiet, ?_⟩⟩
    rw [action]
    rfl

#print axioms tail_12

theorem tail_13 (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rd : BitVec 5) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rm : Rm.toNat < 31) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (N1D226.AdcZeroRn64Generic.Encoding.selected Rd Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (N1D226.AdcZeroRn64Generic.Encoding.selected Rd Rm)
    {} 6 (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd 31#5 Rm 0#1 0#1 1#1) (N1D226.AdcZeroRn64Generic.Tail.noEret Rd Rm)
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_0 Rd 31#5 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, act, hook, metadataInput, _, frame, actionQuiet, action, boundary, _, _⟩ :=
      N1D226.AdcZeroRn64Generic.Progress.action_prefix real source fetched enc0 Rd Rm rd rm
        pins input guard (budget + 1) quiet
    refine ⟨⟨sp, act, hook, metadataInput, boundary, frame, actionQuiet, ?_⟩⟩
    rw [action]
    rfl

#print axioms tail_13

theorem tail_14 (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (imms : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (N1D226.Extr64Generic.Encoding.selected Rd Rn imms Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (N1D226.Extr64Generic.Encoding.selected Rd Rn imms Rm)
    {} 206 (decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate Rd Rn imms Rm 1#1 1#1) (N1D226.Extr64Generic.Tail.noEret Rd Rn imms Rm)
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_15 Rd Rn imms Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    obtain ⟨sp, act, hook, metadataInput, _, frame, actionQuiet, action, boundary, _, _⟩ :=
      N1D226.Extr64Generic.Progress.action_prefix real source fetched enc0 Rd Rn imms Rm rd rn rm
        pins input guard (budget + 1) quiet
    refine ⟨⟨sp, act, hook, metadataInput, boundary, frame, actionQuiet, ?_⟩⟩
    rw [action]
    rfl

#print axioms tail_14

end TranslateScalarTagCheck.Runtime
