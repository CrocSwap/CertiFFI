import ReleaseProfile.GB10.HeapC2NormalSeal

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

/-!
# Oracle independence of the sealed Heap normal C2

The sealed C2 instantiates `OracleChoice` (the values Sail draws from the oracle in the EL2&0 walk: params
dc dct nv1 t0sz t1sz uwxn mair2 pir pire0, and the reference-control mirrors mair2 uwxn) with zeros
(`HeapWorldData.oracle`). This module proves, in the kernel, that nothing depends on that choice:

* `sourceSpec_withOracle`: SourceSpec is invariant under replacing the 11 oracle fields by ANY value;
* `heap_normal_residual_all`: the sealed normal residual (every retained atom, incl. images/walk/permission
  checks) holds at EVERY source-pinned spec with the world tables;
* `heap_normal_residual_every_oracle`: hence it holds at `withOracle spec o` for every oracle choice `o`;
* `heap_normal_c2_at`: the positive C2 reduction itself goes through with any `o` in place of zeros.
-/

namespace ReleaseProfile.GB10

/-- A spec with its 11 oracle-chosen fields replaced by `o`. -/
def withOracle {domain : ArmCert.Translate.Model.QueryDomain} (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (o : OracleChoice) : ArmCert.Translate.Model.TopologyImageSpec domain :=
  { spec with params := { spec.params with dc := o.dc, dct := o.dct, nv1 := o.nv1, t0sz := o.t0sz, t1sz := o.t1sz, uwxn := o.uwxn, mair2 := o.mair2, pir := o.pir, pire0 := o.pire0 }, controls := { spec.controls with mair2 := o.controlsMair2, uwxn := o.controlsUwxn } }

theorem normalizeWalkParams_oracle (regs : ArmFull.Regs) (p : ArmFull.S1TTWParams) (o : OracleChoice) :
    ArmCertWalk.normalizeWalkParams regs { p with dc := o.dc, dct := o.dct, nv1 := o.nv1, t0sz := o.t0sz, t1sz := o.t1sz, uwxn := o.uwxn, mair2 := o.mair2, pir := o.pir, pire0 := o.pire0 } =
    { ArmCertWalk.normalizeWalkParams regs p with dc := o.dc, dct := o.dct, nv1 := o.nv1, t0sz := o.t0sz, t1sz := o.t1sz, uwxn := o.uwxn, mair2 := o.mair2, pir := o.pir, pire0 := o.pire0 } := by
  unfold ArmCertWalk.normalizeWalkParams
  by_cases h1 : (p.txsz.toNat : Int) < 16
  · simp only [h1, if_true]
  · by_cases h2 : (p.txsz.toNat : Int) > ArmCertWalk.currentMaxTxsz regs
    · simp only [h1, h2, if_true, if_false]
    · simp only [h1, h2, if_false]

#check "CURRENT_DECL GB10.sourceSpec_withOracle"
/-- SourceSpec does not constrain the oracle-chosen fields: it is preserved by any oracle replacement. -/
theorem sourceSpec_withOracle {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}
    {domain : ArmCert.Translate.Model.QueryDomain} {spec : ArmCert.Translate.Model.TopologyImageSpec domain}
    (h : SourceSpec rho caller spec) (o : OracleChoice) : SourceSpec rho caller (withOracle spec o) where
  physical := h.physical
  regime := h.regime
  ha := h.ha
  hd := h.hd
  pie := h.pie
  hpd := h.hpd
  pir := h.pir
  pire0 := h.pire0
  overlay := h.overlay
  paramsHa := h.paramsHa
  paramsHd := h.paramsHd
  paramsPie := h.paramsPie
  paramsWxn := h.paramsWxn
  paramsMtx := h.paramsMtx
  normalizedTxsz := h.normalizedTxsz
  guardTbi := h.guardTbi
  guardTbid := h.guardTbid
  guardNfd := h.guardNfd
  guardE0pd := h.guardE0pd
  paramsHaft := h.paramsHaft
  paramsSail := by
    intro d state sail next hr hn
    show { spec.params with dc := o.dc, dct := o.dct, nv1 := o.nv1, t0sz := o.t0sz, t1sz := o.t1sz, uwxn := o.uwxn, mair2 := o.mair2, pir := o.pir, pire0 := o.pire0 } = _
    rw [h.paramsSail d state sail next hr hn]
    exact (normalizeWalkParams_oracle state.regs _ o).symm
  controlsSail := h.controlsSail
  featXS := h.featXS
  mte2 := h.mte2
  paBits := h.paBits
  el2Enabled := h.el2Enabled
  por := h.por
  porE0 := h.porE0
  pan := h.pan
  nv1 := h.nv1
  rawFault := h.rawFault

end ReleaseProfile.GB10

namespace ReleaseProfile.GB10.Heap.Normal

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap

#check "CURRENT_DECL GB10.Heap.Normal.heap_normal_residual_all"
/-- The sealed normal residual at EVERY source-pinned spec with the world tables (any oracle fields). -/
theorem heap_normal_residual_all (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) (spec : ArmCert.Translate.Model.TopologyImageSpec (fun q => ∃ q0 ∈ HeapWorldTables.queries, ArmCertWalk.SamePage q0.va q.va))
    (sspec : SourceSpec rho caller spec) (hlay : spec.layout = HeapWorldTables.tables.layout)
    (hlr : spec.logicalRows = HeapWorldTables.tables.logicalRows)
    (hir : spec.imageRows = HeapWorldTables.tables.imageRows)
    (timers : TimersQuiet (worldEntry worldSemantics rho caller W pcount).regs W.budget) :
    NormalResidual spec W.rows W.mapping W.pins W.scope W.image W.loadBase W.base W.offS W.budget rho caller
      (worldEntry worldSemantics rho caller W pcount) :=
      have imgs := world_images rho caller pcount sspec hir
      have st : StaticsAtP rho caller pcount spec :=
        have cl : ClosedAt rho caller pcount spec := ⟨HeapClosedB.a122 rho caller pcount sspec hlay hlr hir⟩
        {
          a20 := StaticInst.a20,
          a122 := cl.a122,
          a123 := StaticInst.a123 rho caller pcount,
          a244 := StaticInst.a244 hir,
          a256 := StaticInst.a256 rho caller pcount,
          a258 := StaticInst.a258 hir,
          a260 := StaticInst.a260 hir hlr,
          a262 := StaticInst.a262,
          a263 := StaticInst.a263 rho caller pcount,
          a267 := StaticInst.a267,
          a268 := StaticInst.a268
        }
      {
        timers := timers,
        a16 := a16,
        a17 := a17,
        a18 := a18,
        a19 := a19,
        a20 := st.a20,
        a55 := ⟨imgs.1.covered⟩,
        a56 := ⟨imgs.1.topology⟩,
        a57 := ⟨imgs.1.attributes⟩,
        a58 := ⟨imgs.1.writeback⟩,
        a59 := ⟨imgs.1.permissions⟩,
        a121 := a121 rho caller pcount,
        a122 := st.a122,
        a123 := st.a123,
        a210 := ⟨imgs.2⟩,
        a211 := a211 rho caller pcount sspec hir,
        a243 := a243 rho caller pcount,
        a244 := st.a244,
        a245 := a245,
        a246 := a246,
        a256 := st.a256,
        a257 := a257 rho caller pcount,
        a258 := st.a258,
        a259 := a259,
        a260 := ⟨ReleaseProfile.GB10.BodyStaticR.ofFull st.a260.holds⟩,
        a261 := a261,
        a262 := st.a262,
        a263 := st.a263,
        a264 := a264 rho caller pcount,
        a265 := a265 rho caller pcount,
        a266 := a266 rho caller pcount,
        a267 := st.a267,
        a268 := st.a268,
        a269 := a269 rho caller pcount,
        a270 := a270 rho caller pcount,
        a271 := a271,
        a272 := ⟨F21.ndSlot_world⟩,
        a273 := ⟨F21.layout_world⟩,
        a274 := a274 spec
      }

#check "CURRENT_DECL GB10.Heap.Normal.heap_normal_residual_every_oracle"
/-- Oracle independence: for every oracle choice `o`, the residual holds at the oracle-replaced spec. -/
theorem heap_normal_residual_every_oracle (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (o : OracleChoice) (pcount : BitVec 88) (spec : ArmCert.Translate.Model.TopologyImageSpec (fun q => ∃ q0 ∈ HeapWorldTables.queries, ArmCertWalk.SamePage q0.va q.va))
    (sspec : SourceSpec rho caller spec) (hlay : spec.layout = HeapWorldTables.tables.layout)
    (hlr : spec.logicalRows = HeapWorldTables.tables.logicalRows)
    (hir : spec.imageRows = HeapWorldTables.tables.imageRows)
    (timers : TimersQuiet (worldEntry worldSemantics rho caller W pcount).regs W.budget) :
    NormalResidual (withOracle spec o) W.rows W.mapping W.pins W.scope W.image W.loadBase W.base W.offS W.budget
      rho caller (worldEntry worldSemantics rho caller W pcount) :=
  heap_normal_residual_all rho caller pcount (withOracle spec o) (sourceSpec_withOracle sspec o) hlay hlr hir timers

#check "CURRENT_DECL GB10.Heap.Normal.heap_normal_c2_at"
/-- The positive normal C2 reduction with ANY oracle choice in place of the sealed zeros. -/
theorem heap_normal_c2_at (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (o : OracleChoice) :
    NormalC2 rho caller :=
  normal_c2_of_world rho caller worldSemantics W timers_disabled HeapWorldTables.tables o
    (heap_normal_residual_all rho caller)

end ReleaseProfile.GB10.Heap.Normal

#print axioms ReleaseProfile.GB10.sourceSpec_withOracle
#print axioms ReleaseProfile.GB10.Heap.Normal.heap_normal_residual_all
#print axioms ReleaseProfile.GB10.Heap.Normal.heap_normal_residual_every_oracle
#print axioms ReleaseProfile.GB10.Heap.Normal.heap_normal_c2_at
