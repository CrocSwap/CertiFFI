-- Closed concrete shim decoder choices and the two actual stack-update tails.
import NativeShimChoiceTagCheck.Bindings
import HeapV2StepCerts.RegValE
import DefaultScalarTrace
import HeapScalarTagCheck.Tails
import DitShim243.StackClasses

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 1024

open ReleaseProfile
namespace DitShim243.Choice

theorem bti (real : Type) [Sail.SailReal real] (source : NativeState) :
    DefaultScalarTrace.TailChoiceAt real source NativeEntryDispatch.BtiC.word :=
  NativeShimChoiceTagCheck.btiC_choice real source

theorem mrs (real : Type) [Sail.SailReal real] (source : NativeState)
    (profile : NativeEntryAdapters.MrsDit.Profile source) :
    DefaultScalarTrace.TailChoiceAt real source (NativeEntryDispatch.MrsDit.word 9#5) :=
  NativeShimChoiceTagCheck.mrsDit9_choice real source profile

theorem dit_on (real : Type) [Sail.SailReal real] (source : NativeState)
    (profile : NativeEntryAdapters.DitOn.Profile source) :
    DefaultScalarTrace.TailChoiceAt real source NativeEntryDispatch.DitOn.word :=
  NativeShimChoiceTagCheck.ditOn_choice real source profile

theorem isb (real : Type) [Sail.SailReal real] (source : NativeState)
    (profile : NativeEntryAdapters.IsbSy.Profile source) :
    DefaultScalarTrace.TailChoiceAt real source NativeEntryDispatch.IsbSy.word :=
  NativeShimChoiceTagCheck.isbSy_choice real source profile

theorem msr (real : Type) [Sail.SailReal real] (source : NativeState)
    (profile : NativeEntryAdapters.MsrDit.Profile source) :
    DefaultScalarTrace.TailChoiceAt real source (NativeEntryDispatch.MsrDit.word 9#5) :=
  NativeShimChoiceTagCheck.msrDit9_choice real source profile

theorem sub_sp (real : Type) [Sail.SailReal real] (source : NativeState) :
    DefaultScalarTrace.TailChoiceAt real source DitShim243.StackClasses.w1 :=
  HeapScalarTagCheck.Tails.tail_22 real source 16#12 ⟨⟩ DitShim243.StackClasses.noEret1

theorem add_sp (real : Type) [Sail.SailReal real] (source : NativeState) :
    DefaultScalarTrace.TailChoiceAt real source DitShim243.StackClasses.w8 := by
  apply DefaultScalarTrace.tail_choice_of_prefix real source DitShim243.StackClasses.w8
    NativeEntryBodyAdapters.AddSpRestore.writes 18
    (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate
      31#5 31#5 16#12 0#1 0#1 0#1 1#1) DitShim243.StackClasses.noEret8
  · intro state input value after run
    exact HeapScalarTagCheck.Actions.action_2 31#5 31#5 16#12 state value after run
  · intro fetched enc budget pins input guard quiet
    apply Classical.choice
    obtain ⟨sp, action, hook, metadataInput, _, _, boundary, _, frame, actionQuiet, _, _, _, _, result⟩ :=
      RootV.AddSpRestore.action_prefixV real source fetched enc 16#12 ⟨⟩ pins input guard (budget + 1) quiet
    exact ⟨⟨sp, action, hook, metadataInput, boundary, frame, actionQuiet, result⟩⟩

theorem tail1 (real : Type) [Sail.SailReal real] (source : NativeState) :
    RegValE.ClassTailVAt real DitShim243.StackClasses.w1 DitShim243.StackClasses.writes1 DitShim243.StackClasses.K1 source
      (source.regs._PC + 4#64) DitShim243.StackClasses.us1 :=
  RegValE.ClassTailV.at (RootVE.SubSp64.SubSp64_tailV real source 16#12 DitShim243.StackClasses.noEret1 ⟨⟩)

theorem tail8 (real : Type) [Sail.SailReal real] (source : NativeState) :
    RegValE.ClassTailVAt real DitShim243.StackClasses.w8 DitShim243.StackClasses.writes8 DitShim243.StackClasses.K8 source
      (source.regs._PC + 4#64) DitShim243.StackClasses.us8 :=
  RegValE.ClassTailV.at (RootVE.AddSpRestore.AddSpRestore_tailV real source 16#12 DitShim243.StackClasses.noEret8 ⟨⟩)

#print axioms bti
#print axioms mrs
#print axioms dit_on
#print axioms isb
#print axioms msr
#print axioms sub_sp
#print axioms add_sp
#print axioms tail1
#print axioms tail8
end DitShim243.Choice
