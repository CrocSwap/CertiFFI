import Bridge.CruxNonProj
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
namespace NativeEntry.Effects
open ArmBridge.Draft ArmBridge.CruxNonProj
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- Once-generic candidate for the SINGLE canonical action footprint.
The fixed class generator selects the footprint and proves the actual effect.
No caller chooses permissions or supplies a future action/frame result.
This is a register projection contract, not another execution engine. -/
structure Writes where
  dit : Bool := false
  vector : Bool := false
  fpsr : Bool := false
  fpcr : Bool := false

def erase (writes : Writes) (r : Regs) : Regs :=
  { r with
    PSTATE := if writes.dit then { r.PSTATE with DIT := 0#1 } else r.PSTATE
    _Z := if writes.vector then default else r._Z
    FPSR := if writes.fpsr then 0#64 else r.FPSR
    FPCR := if writes.fpcr then 0#64 else r.FPCR }

def mask (writes : Writes) (r : Regs) : Regs := erase writes (ArmCertCT.CT2.mask bkHeap r)

def Frame (writes : Writes) (before after : Regs) : Prop := mask writes after = mask writes before

theorem scalar_iff (before after : Regs) :
    Frame {} before after ↔ ArmCertCT.CT2.NonProjRegsEq bkHeap before after := by rfl

theorem of_scalar (writes : Writes) {before after : Regs}
    (frame : ArmCertCT.CT2.NonProjRegsEq bkHeap before after) : Frame writes before after :=
  congrArg (erase writes) frame

theorem Frame.trans {writes : Writes} {a b c : Regs}
    (left : Frame writes a b) (right : Frame writes b c) : Frame writes a c :=
  Eq.trans right left

theorem dit_update (r : Regs) (bit : BitVec 1) :
    Frame { dit := true } r { r with PSTATE := { r.PSTATE with DIT := bit } } := by rfl

theorem bti_update (r : Regs) (compatible : Bool) (next : BitVec 2) :
    Frame {} r { r with BTypeCompatible := compatible, BTypeNext := next } := by rfl

theorem fpsr_update (r : Regs) (value : BitVec 64) :
    Frame { fpsr := true } r { r with FPSR := value } := by rfl

theorem fpcr_update (r : Regs) (value : BitVec 64) :
    Frame { fpcr := true } r { r with FPCR := value } := by rfl

/- Input controls are transported from the actual prelude. The current memory
snapshot is deliberately absent: fetch/walk writes must retain actual post-memory.
The canonical mask already erases BTypeNext, so its input equality is separate.
GPR/SP/PSTATE/PC source relations remain the canonical input schema's other fields. -/
structure ControlInput (source current : NativeState) : Prop where
  nonProj : ArmCertCT.CT2.NonProjRegsEq bkHeap source.regs current.regs
  btn : current.regs.BTypeNext = source.regs.BTypeNext

theorem ControlInput.bank64 {source current : NativeState} (h : ControlInput source current)
    (key : Bank_BitVec_64) (preserved : bkHeap.b64 key = false) :
    current.regs.bank_BitVec_64 key = source.regs.bank_BitVec_64 key :=
  h.nonProj.bank64 key preserved

theorem ControlInput.bankInt {source current : NativeState} (h : ControlInput source current)
    (key : Bank_Int) (preserved : bkHeap.int key = false) :
    current.regs.bank_Int key = source.regs.bank_Int key := by
  have field := congrFun (congrArg Regs.bank_Int h.nonProj) key
  simpa [ArmCertCT.CT2.mask, ArmCertCT.CT2.maskBank, preserved] using field

theorem ControlInput.features {source current : NativeState} (h : ControlInput source current) :
    current.regs.FeatureImpl = source.regs.FeatureImpl := by
  simpa only [ArmCertCT.CT2.mask] using congrArg Regs.FeatureImpl h.nonProj

theorem ControlInput.refl (source : NativeState) : ControlInput source source := ⟨rfl, rfl⟩

theorem ControlInput.trans {a b c : NativeState}
    (left : ControlInput a b) (right : ControlInput b c) : ControlInput a c :=
  ⟨ArmCertCT.CT2.NonProjRegsEq.trans left.nonProj right.nonProj, right.btn.trans left.btn⟩

#print axioms scalar_iff
#print axioms of_scalar
#print axioms Frame.trans
#print axioms dit_update
#print axioms bti_update
#print axioms fpsr_update
#print axioms fpcr_update
#print axioms ControlInput.bank64
#print axioms ControlInput.bankInt
#print axioms ControlInput.features
#print axioms ControlInput.refl
#print axioms ControlInput.trans
end NativeEntry.Effects
