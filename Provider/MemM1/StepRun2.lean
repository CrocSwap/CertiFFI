import MemM1.StepInv2
import BridgeV2.BoundaryV2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace MemM1.StepRun2
abbrev State := SequentialState Regs oracleChoiceSource
open ArmCert.Eval.M1a.TB (Host20T)
open ArmCert.Premises.TranslationAgreesV3
open ArmBridge.BoundaryV2 (UnmappedSame MappedPA)
open MemM1.WalkKE (walkK)
open MemM1.ConsumerV2 (Page kmap)
open MemM1.StepInv2 (SysEq2 PathIn agreesV3_step)

/-- Table bytes are preserved by any step that keeps unmapped RAM (BoundaryV2.UnmappedSame, which
    the transport concludes per step) when the table bytes lie outside the map's PAs. -/
theorem tb_of_unmapped (P : BitVec 64 → Option Page) (TB : Nat → Prop) (s s' : State)
    (hU : UnmappedSame (kmap P) s s') (hTB : ∀ a, TB a → ¬ MappedPA (kmap P) a) :
    ∀ a, TB a → s'.mem[a]? = s.mem[a]? :=
  fun a h => hU a (hTB a h) id

/-- Run-step form: the start state's kmap-instance inputs, a step that keeps the system registers
    (SysEq2) and unmapped RAM (UnmappedSame), and tables outside the mapped PAs give E17 v3 at the
    new state with the SAME (start-fixed) walk function. -/
theorem agreesV3_run_step (s s' : State) (hR : MemM1.Witness.Regs20 s.regs)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (hI : _get_SCTLR_EL2_Type_I (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (hH : Host20T s)
    (hEPD0 : _get_TCR_EL2_Type_EPD0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1)
    (P : BitVec 64 → Option Page) (TB : Nat → Prop)
    (hP : ∀ (va : BitVec 64) (p : Page), va.toNat < 2^48 → P (va >>> 12) = some p →
      PathIn s va p.leaf TB ∧
        (if p.code then MemM1.WalkFactV.LeafBitsC p.leaf else MemM1.ConsumerD.LeafBitsD p.leaf))
    (hTB : ∀ a, TB a → ¬ MappedPA (kmap P) a)
    (hsys : SysEq2 s.regs s'.regs) (hU : UnmappedSame (kmap P) s s') :
    TranslationAgrees (kmap P) (walkK s.regs s.mem) s' :=
  agreesV3_step s s' hR hC hI hH hEPD0 P TB hP hsys (tb_of_unmapped P TB s s' hU hTB)

/-- Chained form: SysEq2 and UnmappedSame are transitive along a run, so every step state of a run
    from s keeps E17 v3 with walk fixed at s. -/
theorem unmapped_trans (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (s1 s2 s3 : State)
    (h12 : UnmappedSame m s1 s2) (h23 : UnmappedSame m s2 s3) : UnmappedSame m s1 s3 :=
  fun p hm ht => (h23 p hm ht).trans (h12 p hm ht)

/-- One step's register bookkeeping before the fetch (preFetchRegs), then the fetch
    wrapper's writes (fetchRegs) and the IFETCH translation's clrGP keep SysEq2. -/
theorem sysEq2_fetch_chain (r : Regs) :
    SysEq2 r (MemM1.IF.clrGP (ArmCert.Eval.M1a.Fetch2.fetchRegs (MemM1.StepInv2.preFetchRegs r))) :=
  ((MemM1.StepInv2.SysEq2_of_preFetch r).trans (MemM1.StepInv2.SysEq2_of_fetchRegs _)).trans
    (MemM1.StepInv2.SysEq2_of_clrGP _)

#print axioms sysEq2_fetch_chain
#print axioms tb_of_unmapped
#print axioms agreesV3_run_step
#print axioms unmapped_trans
end MemM1.StepRun2
