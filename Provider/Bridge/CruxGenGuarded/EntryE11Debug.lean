import NativeEntryTail.Guard
import MemM1.Debug
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded.E11Debug
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! Approved premise E11, active defects v1.7.41
(premises-draft-v1.7.md SHA cbc271c12a58e49acd8e2cec88d47b7dc90a857fd466e78268d1a4b738360b6e),
formalized EXACTLY as worded as bit predicates on the actual state.
This is a formalization of an approved premise, not a new premise.
OSLSR.OSLK is NOT assumed. The E12 STATUS pin is included only because E11's
text says "EDSCR.STATUS non-debug per E12". -/

/-- E11 as a predicate on the actual register file. -/
structure E11At (r : Regs) : Prop where
  /-- external invasive debug off: DBGEN, SPIDEN, NIDEN low. -/
  dbgen : r.bank_Signal .DBGEN = .Signal_Low
  spiden : r.bank_Signal .SPIDEN = .Signal_Low
  niden : r.bank_Signal .NIDEN = .Signal_Low
  /-- no halting debugger: EDSCR.HDE = 0, EDSCR.STATUS non-debug (E12). -/
  hde : _get_EDSCR_Type_HDE (r.bank_BitVec_32 ._EDSCR) = 0#1
  status : _get_EDSCR_Type_STATUS (r.bank_BitVec_32 ._EDSCR) = 0b000010#6
  /-- no software breakpoints/watchpoints: MDSCR_EL1.MDE = 0, KDE = 0. -/
  mde : _get_MDSCR_EL1_Type_MDE (r.bank_BitVec_64 .MDSCR_EL1) = 0#1
  kde : _get_MDSCR_EL1_Type_KDE (r.bank_BitVec_64 .MDSCR_EL1) = 0#1
  /-- no software single-step. -/
  mdss : _get_MDSCR_EL1_Type_SS (r.bank_BitVec_64 .MDSCR_EL1) = 0#1
  pss : r.PSTATE.SS = 0#1
  /-- no pending external debug event; SPE buffer disabled. -/
  edesr : r.bank_BitVec_32 .EDESR = 0#32
  pmbe : _get_PMBLIMITR_EL1_Type_E (r.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1
  /-- no SPE sample in flight at entry. -/
  spe : r.bank_Bool .SPESampleInFlight = false
  /-- no profiling-buffer service event pending. -/
  pmbs : _get_PMBSR_EL1_Type_S (r.bank_BitVec_64 .PMBSR_EL1) = 0#1
  /-- reset catch disabled. -/
  edecr : _get_EDECR_Type_RCE (r.bank_BitVec_32 .EDECR) = 0#1
  cti : _get_CTIDEVCTL_Type_RCE (r.bank_BitVec_32 .CTIDEVCTL) = 0#1

/-- The two E11 bits that `AArch64_CheckDebug` reads to decide on
breakpoint/watchpoint generation and halting. -/
structure E11CheckDebug (r : Regs) : Prop where
  mde : _get_MDSCR_EL1_Type_MDE (r.bank_BitVec_64 .MDSCR_EL1) = 0#1
  hde : _get_EDSCR_Type_HDE (r.bank_BitVec_32 ._EDSCR) = 0#1

theorem E11At.checkDebug {r : Regs} (e : E11At r) : E11CheckDebug r := ⟨e.mde, e.hde⟩

/-- Registers whose equality carries `E11CheckDebug` across a step. -/
theorem E11CheckDebug.transfer {r r' : Regs} (e : E11CheckDebug r)
    (h64 : r'.bank_BitVec_64 .MDSCR_EL1 = r.bank_BitVec_64 .MDSCR_EL1)
    (h32 : r'.bank_BitVec_32 ._EDSCR = r.bank_BitVec_32 ._EDSCR) : E11CheckDebug r' :=
  ⟨h64 ▸ e.mde, h32 ▸ e.hde⟩

/-- Every E11 bit that EntryPins22 already carries is a projection of E11. -/
theorem E11At.entry_overlap {r : Regs} (e : E11At r) :
    r.bank_Bool .SPESampleInFlight = false ∧
    _get_EDECR_Type_RCE (r.bank_BitVec_32 .EDECR) = 0#1 ∧
    _get_CTIDEVCTL_Type_RCE (r.bank_BitVec_32 .CTIDEVCTL) = 0#1 ∧
    _get_EDSCR_Type_STATUS (r.bank_BitVec_32 ._EDSCR) = 0b000010#6 ∧
    r.bank_BitVec_32 .EDESR = 0#32 ∧
    _get_PMBLIMITR_EL1_Type_E (r.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1 ∧
    _get_MDSCR_EL1_Type_SS (r.bank_BitVec_64 .MDSCR_EL1) = 0#1 ∧
    Sail.BitVec.extractLsb (r.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1 ∧
    r.PSTATE.SS = 0#1 :=
  ⟨e.spe, e.edecr, e.cti, e.status, e.edesr, e.pmbe, e.mdss, e.pmbs, e.pss⟩

/-- E11 from the nine overlapping EntryPins fields plus the remaining E11 bits
named in its text; no other field is required. -/
theorem E11At.of_entry {s : NativeState} (pins : NativeEntryTail.EntryPins s)
    (dbgen : s.regs.bank_Signal .DBGEN = .Signal_Low)
    (spiden : s.regs.bank_Signal .SPIDEN = .Signal_Low)
    (niden : s.regs.bank_Signal .NIDEN = .Signal_Low)
    (hde : _get_EDSCR_Type_HDE (s.regs.bank_BitVec_32 ._EDSCR) = 0#1)
    (mde : _get_MDSCR_EL1_Type_MDE (s.regs.bank_BitVec_64 .MDSCR_EL1) = 0#1)
    (kde : _get_MDSCR_EL1_Type_KDE (s.regs.bank_BitVec_64 .MDSCR_EL1) = 0#1) :
    E11At s.regs :=
  ⟨dbgen, spiden, niden, hde, pins.st, mde, kde, pins.mdss, pins.pss, pins.edesr,
    pins.pmbe, pins.spe, pins.pmbs, pins.edecr, pins.cti⟩

run_cmd do
  IO.eprintln "CURRENT_DECL E11Debug.check_debug_no_fault"
  (← IO.getStderr).flush

/-- `AArch64_CheckDebug` is a no-op on any actual state satisfying E11's
MDE/HDE bits: Fault_None and only choice state changes. The remaining
hypotheses are the non-debug EntryPins fields (E1 EL0, E19 RME absent,
F6 FeatureImpl[4], SCR_EL3.NS) used only to resolve the security state;
no debug bit outside E11's text is needed. -/
theorem check_debug_no_fault (va : BitVec 64) (acc : AccessDescriptor) (size : Int)
    (s : NativeState) (debug : E11CheckDebug s.regs)
    (el : s.regs.PSTATE.EL = 0#2) (rme : s.regs.FeatureImpl[232]! = false)
    (f4 : s.regs.FeatureImpl[4]! = true)
    (scrns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1) :
    ∃ fault t, AArch64_CheckDebug va acc size s = .ok fault t ∧
      fault.statuscode = .Fault_None ∧ S1Normality.Frame s t := by
  have rme' : s.regs.FeatureImpl[232] = false := by simpa using rme
  have f4' : s.regs.FeatureImpl[4] = true := by simpa using f4
  exact MemM1.Debug.no_fault va acc size s el rme' f4' scrns debug.mde debug.hde

/-- Entry-state instance from EntryPins22 plus E11. -/
theorem entry_check_debug_no_fault (va : BitVec 64) (acc : AccessDescriptor) (size : Int)
    (s : NativeState) (pins : NativeEntryTail.EntryPins s) (e11 : E11At s.regs) :
    ∃ fault t, AArch64_CheckDebug va acc size s = .ok fault t ∧
      fault.statuscode = .Fault_None ∧ S1Normality.Frame s t :=
  check_debug_no_fault va acc size s e11.checkDebug pins.el pins.rme pins.f4 pins.scrns

#print axioms E11At.of_entry
#print axioms E11CheckDebug.transfer
#print axioms check_debug_no_fault
#print axioms entry_check_debug_no_fault
end ArmBridge.CruxGenGuarded.E11Debug
