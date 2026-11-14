import PipeSecpSubPlan.Plan
import ArmCertValue.EntrySnapshot
import ArmCertPipe.FPrefix
set_option autoImplicit false
namespace PipeSecpSubPlan
open ArmCertValue HeapV2StepCerts.RegBind

def entryInputs_c05 (view : Physical.BytePA) (entry : St) : List (BitVec 64) :=
  mkInputsL entry rs_c05 (Physical.Entry.snapshot view entry rs_c05)
theorem entryInputs_length_c05 (view : Physical.BytePA) (entry : St) :
    (entryInputs_c05 view entry).length = n0_c05 :=
  Physical.Entry.snapshot_inputs_length view entry rs_c05
theorem entry_agrees_c05 (view : Physical.BytePA) (entry : St)
    (present : ∀ g j i k, memBL rs_c05 0 g j = some (i,k) →
      (Physical.regionByte view entry g j).isSome = true) :
    Physical.Agrees view (entryInputs_c05 view entry) σ0_c05 entry :=
  Physical.Entry.snapshot_agrees view entry rs_c05 present
theorem entry_bounded_c05 (view : Physical.BytePA) (entry : St) :
    σ0_c05.Bounded (entryInputs_c05 view entry).length :=
  Physical.Entry.snapshot_bounded view entry rs_c05
theorem entry_prefix_c05 (view : Physical.BytePA) (entry : St) (tp : BitVec 64)
    (present : ∀ g j i k, memBL rs_c05 0 g j = some (i,k) →
      (Physical.regionByte view entry g j).isSome = true) :
    ArmCertPipe.F.AgreesAt view regions_c05 σ0_c05 (entryInputs_c05 view entry) (plan_c05 tp) 0 entry :=
  ArmCertPipe.F.agreesAt_zero (entry_agrees_c05 view entry present) (entry_bounded_c05 view entry)
#print axioms entryInputs_length_c05
#print axioms entry_agrees_c05
#print axioms entry_bounded_c05
#print axioms entry_prefix_c05

def entryInputs_c06 (view : Physical.BytePA) (entry : St) : List (BitVec 64) :=
  mkInputsL entry rs_c06 (Physical.Entry.snapshot view entry rs_c06)
theorem entryInputs_length_c06 (view : Physical.BytePA) (entry : St) :
    (entryInputs_c06 view entry).length = n0_c06 :=
  Physical.Entry.snapshot_inputs_length view entry rs_c06
theorem entry_agrees_c06 (view : Physical.BytePA) (entry : St)
    (present : ∀ g j i k, memBL rs_c06 0 g j = some (i,k) →
      (Physical.regionByte view entry g j).isSome = true) :
    Physical.Agrees view (entryInputs_c06 view entry) σ0_c06 entry :=
  Physical.Entry.snapshot_agrees view entry rs_c06 present
theorem entry_bounded_c06 (view : Physical.BytePA) (entry : St) :
    σ0_c06.Bounded (entryInputs_c06 view entry).length :=
  Physical.Entry.snapshot_bounded view entry rs_c06
theorem entry_prefix_c06 (view : Physical.BytePA) (entry : St) (tp : BitVec 64)
    (present : ∀ g j i k, memBL rs_c06 0 g j = some (i,k) →
      (Physical.regionByte view entry g j).isSome = true) :
    ArmCertPipe.F.AgreesAt view regions_c06 σ0_c06 (entryInputs_c06 view entry) (plan_c06 tp) 0 entry :=
  ArmCertPipe.F.agreesAt_zero (entry_agrees_c06 view entry present) (entry_bounded_c06 view entry)
#print axioms entryInputs_length_c06
#print axioms entry_agrees_c06
#print axioms entry_bounded_c06
#print axioms entry_prefix_c06

def entryInputs_c07 (view : Physical.BytePA) (entry : St) : List (BitVec 64) :=
  mkInputsL entry rs_c07 (Physical.Entry.snapshot view entry rs_c07)
theorem entryInputs_length_c07 (view : Physical.BytePA) (entry : St) :
    (entryInputs_c07 view entry).length = n0_c07 :=
  Physical.Entry.snapshot_inputs_length view entry rs_c07
theorem entry_agrees_c07 (view : Physical.BytePA) (entry : St)
    (present : ∀ g j i k, memBL rs_c07 0 g j = some (i,k) →
      (Physical.regionByte view entry g j).isSome = true) :
    Physical.Agrees view (entryInputs_c07 view entry) σ0_c07 entry :=
  Physical.Entry.snapshot_agrees view entry rs_c07 present
theorem entry_bounded_c07 (view : Physical.BytePA) (entry : St) :
    σ0_c07.Bounded (entryInputs_c07 view entry).length :=
  Physical.Entry.snapshot_bounded view entry rs_c07
theorem entry_prefix_c07 (view : Physical.BytePA) (entry : St) (tp : BitVec 64)
    (present : ∀ g j i k, memBL rs_c07 0 g j = some (i,k) →
      (Physical.regionByte view entry g j).isSome = true) :
    ArmCertPipe.F.AgreesAt view regions_c07 σ0_c07 (entryInputs_c07 view entry) (plan_c07 tp) 0 entry :=
  ArmCertPipe.F.agreesAt_zero (entry_agrees_c07 view entry present) (entry_bounded_c07 view entry)
#print axioms entryInputs_length_c07
#print axioms entry_agrees_c07
#print axioms entry_bounded_c07
#print axioms entry_prefix_c07

def entryInputs_c08 (view : Physical.BytePA) (entry : St) : List (BitVec 64) :=
  mkInputsL entry rs_c08 (Physical.Entry.snapshot view entry rs_c08)
theorem entryInputs_length_c08 (view : Physical.BytePA) (entry : St) :
    (entryInputs_c08 view entry).length = n0_c08 :=
  Physical.Entry.snapshot_inputs_length view entry rs_c08
theorem entry_agrees_c08 (view : Physical.BytePA) (entry : St)
    (present : ∀ g j i k, memBL rs_c08 0 g j = some (i,k) →
      (Physical.regionByte view entry g j).isSome = true) :
    Physical.Agrees view (entryInputs_c08 view entry) σ0_c08 entry :=
  Physical.Entry.snapshot_agrees view entry rs_c08 present
theorem entry_bounded_c08 (view : Physical.BytePA) (entry : St) :
    σ0_c08.Bounded (entryInputs_c08 view entry).length :=
  Physical.Entry.snapshot_bounded view entry rs_c08
theorem entry_prefix_c08 (view : Physical.BytePA) (entry : St) (tp : BitVec 64)
    (present : ∀ g j i k, memBL rs_c08 0 g j = some (i,k) →
      (Physical.regionByte view entry g j).isSome = true) :
    ArmCertPipe.F.AgreesAt view regions_c08 σ0_c08 (entryInputs_c08 view entry) (plan_c08 tp) 0 entry :=
  ArmCertPipe.F.agreesAt_zero (entry_agrees_c08 view entry present) (entry_bounded_c08 view entry)
#print axioms entryInputs_length_c08
#print axioms entry_agrees_c08
#print axioms entry_bounded_c08
#print axioms entry_prefix_c08

def entryInputs_c09 (view : Physical.BytePA) (entry : St) : List (BitVec 64) :=
  mkInputsL entry rs_c09 (Physical.Entry.snapshot view entry rs_c09)
theorem entryInputs_length_c09 (view : Physical.BytePA) (entry : St) :
    (entryInputs_c09 view entry).length = n0_c09 :=
  Physical.Entry.snapshot_inputs_length view entry rs_c09
theorem entry_agrees_c09 (view : Physical.BytePA) (entry : St)
    (present : ∀ g j i k, memBL rs_c09 0 g j = some (i,k) →
      (Physical.regionByte view entry g j).isSome = true) :
    Physical.Agrees view (entryInputs_c09 view entry) σ0_c09 entry :=
  Physical.Entry.snapshot_agrees view entry rs_c09 present
theorem entry_bounded_c09 (view : Physical.BytePA) (entry : St) :
    σ0_c09.Bounded (entryInputs_c09 view entry).length :=
  Physical.Entry.snapshot_bounded view entry rs_c09
theorem entry_prefix_c09 (view : Physical.BytePA) (entry : St) (tp : BitVec 64)
    (present : ∀ g j i k, memBL rs_c09 0 g j = some (i,k) →
      (Physical.regionByte view entry g j).isSome = true) :
    ArmCertPipe.F.AgreesAt view regions_c09 σ0_c09 (entryInputs_c09 view entry) (plan_c09 tp) 0 entry :=
  ArmCertPipe.F.agreesAt_zero (entry_agrees_c09 view entry present) (entry_bounded_c09 view entry)
#print axioms entryInputs_length_c09
#print axioms entry_agrees_c09
#print axioms entry_bounded_c09
#print axioms entry_prefix_c09

end PipeSecpSubPlan
