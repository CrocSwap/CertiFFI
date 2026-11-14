import XlateSecp.Raw
import XlateSecp.Topology
import XlateSecp.Cards
import PipeLean_D234_SecpAdd_c00.EntryBinding
import PipeLean_D234_SecpAdd_c01.EntryBinding
import PipeLean_D234_SecpAdd_c02.EntryBinding
import PipeLean_D234_SecpAdd_c03.EntryBinding
import PipeLean_D234_SecpAdd_c04.EntryBinding
import PipeLean_D234_SecpSub_c05.EntryBinding
import PipeLean_D234_SecpSub_c06.EntryBinding
import PipeLean_D234_SecpSub_c07.EntryBinding
import PipeLean_D234_SecpSub_c08.EntryBinding
import PipeLean_D234_SecpSub_c09.EntryBinding
import PipeLean_D234_SecpNeg_c10.EntryBinding
import PipeLean_D234_SecpNeg_c11.EntryBinding
import PipeLean_D234_SecpDouble_c12.EntryBinding
import PipeLean_D234_SecpDouble_c13.EntryBinding
import PipeLean_D234_SecpMul_c14.EntryBinding
import PipeLean_D234_SecpMul_c15.EntryBinding
import PipeLean_D234_SecpMul_c16.EntryBinding
import PipeLean_D234_SecpMul_c17.EntryBinding
import PipeLean_D234_SecpMul_c18.EntryBinding
import PipeLean_D234_SecpMulAlt_c19.EntryBinding
import PipeLean_D234_SecpMulAlt_c20.EntryBinding
import PipeLean_D234_SecpMulAlt_c21.EntryBinding
import PipeLean_D234_SecpMulAlt_c22.EntryBinding
import PipeLean_D234_SecpMulAlt_c23.EntryBinding
import PipeLean_D234_SecpSqr_c24.EntryBinding
import PipeLean_D234_SecpSqr_c25.EntryBinding
import PipeLean_D234_SecpSqrAlt_c26.EntryBinding
import PipeLean_D234_SecpSqrAlt_c27.EntryBinding
import PipeLean_D234_SecpCmul_c28.EntryBinding
import PipeLean_D234_SecpCmul_c29.EntryBinding
import PipeLean_D234_SecpMod4_c30.EntryBinding
import PipeLean_D234_SecpMod4_c31.EntryBinding

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # a125 (SecpRawDeployment.checkLayout) at the source-pinned raw and the World entry, all 32 cards (Translate; generated). checkLayout reads the raw only through layout/imageRows and the entry only through its GPRs. -/

namespace XlateSecp.LayoutAll
open Sail ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ArmBridge.Draft
open ArmBridge.CruxGenGuarded NativeAccess ArmCertValue ArmCertPipe
open ReleaseProfile.MachineSource ReleaseProfile.GB10 TranslateSpan TranslateSpan.SecpRawDeployment XlateSecp.Topology XlateSecp.Cards

def viewG (p : Plan) (mapping : BitVec 64 → Option Nat) (gpr : Vector (BitVec 64) 31) : Physical.BytePA :=
  fun r j => mapping (regionVAG gpr (p.normalize r) j)

def checkLayoutG (p : Plan) (layout : S1LogicalReference.Layout) (imageRows : List ImageRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (gpr : Vector (BitVec 64) 31) : Bool :=
  let outputBytes := p.outputs.flatMap fun (r,n) => StaticLayout.outputPAs (viewG p mapping gpr) r n
  (p.buffers.all fun (r, n) =>
    decide (0 ≤ (gprAt gpr r.pin).toNat + r.off ∧
      (gprAt gpr r.pin).toNat + r.off + (n : Int) ≤ (2 ^ (min 55 layout.inputBits) : Nat)) &&
    (regionVAG gpr r 0 == regionVAG gpr (p.normalize r) 0)) &&
    p.code.all (fun c => decide (base.toNat + c.1 + 4 ≤ 2 ^ (min 55 layout.inputBits))) &&
    StaticLayout.checkInjective (viewG p mapping gpr) (p.regions.map Prod.fst) &&
    StaticLayout.checkCodeAvoid (codeOffsets p) mapping base
      (fun pa => StaticLayout.footprintByte (rowsFootprint imageRows) pa || outputBytes.contains pa) &&
    p.outputs.all (fun (r,n) => StaticLayout.checkOutput (viewG p mapping gpr) r n (rowsFootprint imageRows)) &&
    p.code.all (fun c => StaticLayout.checkCodeWord mapping base c.1)

theorem layout_eq (p : Plan) (raw : CheckedTopology.Raw) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (e : NativeState) : checkLayout p raw mapping base e = checkLayoutG p raw.layout raw.imageRows mapping base e.regs.gpr :=
  rfl

theorem c00_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpAdd_c00.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c00 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c00 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c01_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpAdd_c01.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c01 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c01 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c02_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpAdd_c02.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c02 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c02 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c03_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpAdd_c03.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c03 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c03 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c04_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpAdd_c04.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c04 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c04 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c05_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpSub_c05.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c05 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c05 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c06_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpSub_c06.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c06 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c06 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c07_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpSub_c07.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c07 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c07 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c08_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpSub_c08.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c08 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c08 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c09_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpSub_c09.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c09 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c09 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c10_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpNeg_c10.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c10 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c10 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c11_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpNeg_c11.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c11 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c11 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c12_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpDouble_c12.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c12 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c12 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c13_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpDouble_c13.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c13 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c13 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c14_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpMul_c14.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c14 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c14 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c15_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpMul_c15.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c15 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c15 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c16_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpMul_c16.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c16 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c16 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c17_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpMul_c17.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c17 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c17 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c18_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpMul_c18.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c18 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c18 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c19_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpMulAlt_c19.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c19 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c19 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c20_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpMulAlt_c20.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c20 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c20 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c21_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpMulAlt_c21.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c21 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c21 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c22_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpMulAlt_c22.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c22 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c22 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c23_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpMulAlt_c23.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c23 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c23 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c24_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpSqr_c24.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c24 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c24 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c25_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpSqr_c25.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c25 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c25 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c26_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpSqrAlt_c26.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c26 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c26 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c27_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpSqrAlt_c27.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c27 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c27 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c28_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpCmul_c28.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c28 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c28 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c29_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpCmul_c29.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c29 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c29 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c30_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpMod4_c30.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c30 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c30 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

theorem c31_layout {o : OracleChoice} (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    checkLayout PipeLean_D234_SecpMod4_c31.EntryBinding.plan (XlateSecp.Raw.Ro sem rho caller card_c31 pcount o) World.mapping World.base
      (World.entry sem rho caller card_c31 pcount) = true := by
  rw [layout_eq, XlateSecp.Raw.Ro_layout, XlateSecp.Raw.Ro_imageRows, entry_gpr]
  decide +kernel

end XlateSecp.LayoutAll

#print axioms XlateSecp.LayoutAll.c00_layout
#print axioms XlateSecp.LayoutAll.c01_layout
#print axioms XlateSecp.LayoutAll.c02_layout
#print axioms XlateSecp.LayoutAll.c03_layout
#print axioms XlateSecp.LayoutAll.c04_layout
#print axioms XlateSecp.LayoutAll.c05_layout
#print axioms XlateSecp.LayoutAll.c06_layout
#print axioms XlateSecp.LayoutAll.c07_layout
#print axioms XlateSecp.LayoutAll.c08_layout
#print axioms XlateSecp.LayoutAll.c09_layout
#print axioms XlateSecp.LayoutAll.c10_layout
#print axioms XlateSecp.LayoutAll.c11_layout
#print axioms XlateSecp.LayoutAll.c12_layout
#print axioms XlateSecp.LayoutAll.c13_layout
#print axioms XlateSecp.LayoutAll.c14_layout
#print axioms XlateSecp.LayoutAll.c15_layout
#print axioms XlateSecp.LayoutAll.c16_layout
#print axioms XlateSecp.LayoutAll.c17_layout
#print axioms XlateSecp.LayoutAll.c18_layout
#print axioms XlateSecp.LayoutAll.c19_layout
#print axioms XlateSecp.LayoutAll.c20_layout
#print axioms XlateSecp.LayoutAll.c21_layout
#print axioms XlateSecp.LayoutAll.c22_layout
#print axioms XlateSecp.LayoutAll.c23_layout
#print axioms XlateSecp.LayoutAll.c24_layout
#print axioms XlateSecp.LayoutAll.c25_layout
#print axioms XlateSecp.LayoutAll.c26_layout
#print axioms XlateSecp.LayoutAll.c27_layout
#print axioms XlateSecp.LayoutAll.c28_layout
#print axioms XlateSecp.LayoutAll.c29_layout
#print axioms XlateSecp.LayoutAll.c30_layout
#print axioms XlateSecp.LayoutAll.c31_layout
