import CruxMem.LdrbEval
import Bridge.CruxGen
import MemM1.MemInv
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmCertMem.LdrbPre
open ArmBridge.CruxGen ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1 ArmBridge.CruxCore
open CryptoMem.LdstPost

/-! The CongIn-invariant precondition `Pre` of the LDRB (post-index) leaf: memory's run invariant
`MemInv s0 P4 P2 TB` (SysEq2 to `s0` + unmapped RAM unchanged since `s0`), BEPins, FEAT_EL3 A64/no A32,
and the per-access facts at the address `X[Rn]` (permitted, not MMIO, byte present). -/

/-- The access address: `X[Rn]` of `t`. -/
abbrev addr (t : NativeState) (Rn : BitVec 5) : BitVec 64 := t.regs.gpr[(GPRSummary.key Rn.toNat).val]

structure Pre (s0 : NativeState) (P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page) (TB : Nat → Prop)
    (Rn : BitVec 5) (t : NativeState) : Prop where
  inv : MemM1.MemInv.MemInv s0 P4 P2 TB t
  be : MemM1.MemDataV3.BEPins t.regs
  f7 : t.regs.FeatureImpl[7] = true
  f3 : t.regs.FeatureImpl[3] = false
  perm : ∀ acc, MemM1.Witness.Acc0 acc → (MemM1.ConsumerB.kmapB P4 P2).permitted (addr t Rn) acc true 1
  io : MemM1.MemReadIF.NotMMIO ((MemM1.ConsumerB.kmapB P4 P2).pa (addr t Rn))
  byte : ∃ v : BitVec 8, t.mem[((MemM1.ConsumerB.kmapB P4 P2).pa (addr t Rn)).toNat]? = some v

/-- `CruxCore.SysEq2` (in `CongIn`) as memory's `StepInv2.SysEq2`, oriented `t1 → t2`. -/
theorem sysEq2_of_congIn {t1 t2 : NativeState} (h : CongIn t1 t2) : MemM1.StepInv2.SysEq2 t1.regs t2.regs :=
  ⟨h.sys.feat.symm, h.sys.el.symm, h.sys.nrw.symm, h.sys.sctlr.symm, h.sys.tcr.symm, h.sys.tcr2.symm,
    h.sys.hcr.symm, h.sys.scr.symm, h.sys.mair.symm, h.sys.mdscr.symm, h.sys.httbr.symm, h.sys.ttbr0.symm,
    h.sys.ttbr1.symm, h.sys.hde.symm, h.sys.tlb.symm, h.sys.spe.symm, h.sys.pa.symm⟩

theorem congIn_symm {t1 t2 : NativeState} (h : CongIn t1 t2) : CongIn t2 t1 :=
  ⟨h.mem.symm, h.gpr.symm, h.sp.symm, h.z.symm, h.ps.symm,
    ⟨h.sys.feat.symm, h.sys.el.symm, h.sys.nrw.symm, h.sys.sctlr.symm, h.sys.tcr.symm, h.sys.tcr2.symm,
    h.sys.hcr.symm, h.sys.scr.symm, h.sys.mair.symm, h.sys.mdscr.symm, h.sys.httbr.symm, h.sys.ttbr0.symm,
    h.sys.ttbr1.symm, h.sys.hde.symm, h.sys.tlb.symm, h.sys.spe.symm, h.sys.pa.symm⟩,
    h.spx1.symm, h.spx2.symm, h.spx3.symm, by rw [← h.ps]; exact h.el0⟩

theorem pre_congr {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {Rn : BitVec 5} {t1 t2 : NativeState} (hc : CongIn t1 t2) (h : Pre s0 P4 P2 TB Rn t1) :
    Pre s0 P4 P2 TB Rn t2 := by
  have hs := sysEq2_of_congIn hc
  have hf : t2.regs.FeatureImpl = t1.regs.FeatureImpl := hs.feat
  have ha : addr t2 Rn = addr t1 Rn := by simp only [addr, hc.gpr]
  refine ⟨⟨h.inv.1, h.inv.2.1.trans hs, fun p h1 h2 => by rw [← hc.mem]; exact h.inv.2.2 p h1 h2⟩,
    ⟨by rw [← hc.ps]; exact h.be.el0, by rw [← hc.ps]; exact h.be.nrw, by rw [hf]; exact h.be.noRME,
     by rw [hf]; exact h.be.vhe, by rw [hf]; exact h.be.aa64el0, by rw [hs.scr]; exact h.be.ns,
     by rw [hs.hcr]; exact h.be.e2h, by rw [hs.hcr]; exact h.be.tge⟩,
    by rw [hf]; exact h.f7, by rw [hf]; exact h.f3, by rw [ha]; exact h.perm, by rw [ha]; exact h.io,
    by rw [ha, ← hc.mem]; exact h.byte⟩

#print axioms pre_congr
end ArmCertMem.LdrbPre
