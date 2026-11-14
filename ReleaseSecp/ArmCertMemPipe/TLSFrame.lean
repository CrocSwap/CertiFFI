-- TLS is an observed system field, proved from actual entry/action/epilogue frames.
import HeapV2StepCerts.ValueTailDefE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCertMemPipe.TLSFrame
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)

def tp (s : NativeState) : BitVec 64 := s.regs.bank_BitVec_64 .TPIDR_EL0

theorem nonProj {a fin : NativeState}
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs) : tp fin = tp a := by
  have h := congrFun (ArmBridge.CruxNonProj.mb64 np) Bank_BitVec_64.TPIDR_EL0
  simpa only [tp, ArmCertCT.CT2.maskBank, ArmBridge.CruxNonProj.bkHeap, Bool.false_eq_true, ite_false] using h

theorem tail {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int}
    {sp a fin fetched : NativeState} {budget : Nat}
    (quiet : HookQuiet (budget + 1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp)
    (frame : NativeEntryContract.Frame writes (actionState w sp K) a)
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs) :
    tp fin = tp fetched := by
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  rw [nonProj np]
  unfold tp
  rw [congrFun frame.b64 .TPIDR_EL0]
  show sp.regs.bank_BitVec_64 .TPIDR_EL0 = _
  exact frame_pres_E20 (fun x => x.bank_BitVec_64 .TPIDR_EL0)
    (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame

#print axioms tail
end ArmCertMemPipe.TLSFrame
