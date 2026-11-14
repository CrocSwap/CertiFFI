import Bridge.CruxNonProj
import BridgeV2.BoundaryV2
import Bridge.CruxGenBrDefs
import Crypto.BranchV2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace Crypto.CruxBrObl
open ArmBridge.Draft ArmBridge.CruxGenBr

/-! Generic per-form obligations for `crux_gen_br`.
 The Br structures below copy ws/Bridge/CruxGenBr.lean draft, with two proposed changes:
    `ActFrameBr.bbool` is pointwise except `SPESamplePreviousBranchAddressValid` (BranchTo's SPE path writes it),
    and `PreBr` carries `Branchtypetaken ≠ RESET` (B.cond/CBZ not-taken leave it unchanged). -/

/-- What a branch action does, as explicit functions of the action input: new GPR file (as a state whose `gpr`
    is read), new PC, new `__BranchTaken`. -/
structure BrSpec where
  fG : NativeState → NativeState
  fPC : NativeState → BitVec 64
  fBT : NativeState → Bool

/-- `u` is a well-behaved result of `A` on `t`, matching the spec. -/
structure Good (A : SailM Unit) (F : BrSpec) (t u : NativeState) : Prop where
  ok : A t = .ok () u
  fr : ActFrameBr t u
  mem : u.mem = t.mem
  gpr : u.regs.gpr = (F.fG t).regs.gpr
  sp : u.regs.SP_EL0 = t.regs.SP_EL0
  z : u.regs._Z = t.regs._Z
  ps : u.regs.PSTATE = t.regs.PSTATE
  pc : u.regs._PC = F.fPC t
  bt : u.regs.__BranchTaken = F.fBT t
  btt : u.regs.Branchtypetaken ≠ BranchType.BranchType_RESET
  npe : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs
  gic : u.regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending

/-- The fallback result: the spec's fields written into `t`. -/
def fallback (F : BrSpec) (t : NativeState) : NativeState :=
  { t with regs := { t.regs with gpr := (F.fG t).regs.gpr, _PC := F.fPC t, __BranchTaken := F.fBT t,
                                 Branchtypetaken := BranchType.BranchType_DIR } }

/-- Guarded result map: the action's result where it is well behaved, the fallback elsewhere. -/
noncomputable def Rg (A : SailM Unit) (F : BrSpec) (t : NativeState) : NativeState :=
  haveI := Classical.propDecidable (∃ u, Good A F t u)
  if h : ∃ u, Good A F t u then Classical.choose h else fallback F t

/-- Every field the obligations read, for every `t`. -/
structure RFacts (F : BrSpec) (t u : NativeState) : Prop where
  fr : ActFrameBr t u
  mem : u.mem = t.mem
  gpr : u.regs.gpr = (F.fG t).regs.gpr
  sp : u.regs.SP_EL0 = t.regs.SP_EL0
  z : u.regs._Z = t.regs._Z
  ps : u.regs.PSTATE = t.regs.PSTATE
  pc : u.regs._PC = F.fPC t
  bt : u.regs.__BranchTaken = F.fBT t
  btt : u.regs.Branchtypetaken ≠ BranchType.BranchType_RESET
  npe : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs
  gic : u.regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending

theorem rfacts (A : SailM Unit) (F : BrSpec) (t : NativeState) : RFacts F t (Rg A F t) := by
  unfold Rg
  split
  · next h =>
    have g := Classical.choose_spec h
    exact ⟨g.fr, g.mem, g.gpr, g.sp, g.z, g.ps, g.pc, g.bt, g.btt, g.npe, g.gic⟩
  · exact ⟨⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      (fun h => BranchType.noConfusion h : BranchType.BranchType_DIR ≠ BranchType.BranchType_RESET),
      (by unfold ArmCertCT.CT2.NonProjRegsEq ArmCertCT.CT2.mask fallback; rfl), rfl⟩

theorem rg_ok (A : SailM Unit) (F : BrSpec) (t : NativeState) (h : ∃ u, Good A F t u) : A t = .ok () (Rg A F t) := by
  unfold Rg
  rw [dif_pos h]
  exact (Classical.choose_spec h).ok

/-- The five per-form obligations of `crux_gen_br` for `R := Rg A F`, from:
    `hBRf` (the spec only branches or keeps PC/bt), `hCf` (the spec reads only CongInBr data), and
    `hObs` (on prelude states the action is well behaved). -/
theorem obligations (A : SailM Unit) (F : BrSpec) (s : NativeState)
    (hBRf : ∀ t, (F.fBT t = t.regs.__BranchTaken ∧ F.fPC t = t.regs._PC) ∨ F.fBT t = true)
    (hCf : ∀ t1 t2, CongInBr t1 t2 →
      (F.fG t1).regs.gpr = (F.fG t2).regs.gpr ∧ F.fPC t1 = F.fPC t2 ∧ F.fBT t1 = F.fBT t2)
    (hObs : ∀ t, PreBr s t → ∃ u, Good A F t u) :
    (∀ t, PreBr s t → A t = .ok () (Rg A F t)) ∧ (∀ t, ActFrameBr t (Rg A F t)) ∧
    (∀ t, ((Rg A F t).regs.__BranchTaken = t.regs.__BranchTaken ∧ (Rg A F t).regs._PC = t.regs._PC) ∨
      (Rg A F t).regs.__BranchTaken = true) ∧
    (∀ t, (Rg A F t).regs.Branchtypetaken ≠ BranchType.BranchType_RESET) ∧
    (∀ t1 t2, CongInBr t1 t2 → CongOutBr (Rg A F t1) (Rg A F t2)) := by
  refine ⟨fun t ht => rg_ok A F t (hObs t ht), fun t => (rfacts A F t).fr, fun t => ?_, fun t => (rfacts A F t).btt,
    fun t1 t2 h => ?_⟩
  · have r := rfacts A F t
    rcases hBRf t with ⟨h1, h2⟩ | h1
    · exact Or.inl ⟨r.bt.trans h1, r.pc.trans h2⟩
    · exact Or.inr (r.bt.trans h1)
  · have r1 := rfacts A F t1
    have r2 := rfacts A F t2
    obtain ⟨cg, cp, cb⟩ := hCf t1 t2 h
    have hps : t1.regs.PSTATE = t2.regs.PSTATE := h.base.ps
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [r1.mem, r2.mem]; exact h.base.mem
    · rw [r1.gpr, r2.gpr]; exact cg
    · rw [r1.sp, r2.sp]; exact h.base.sp
    · rw [r1.z, r2.z]; exact h.base.z
    · rw [r1.ps, r2.ps, hps]
    · rw [r1.ps, r2.ps, hps]
    · rw [r1.ps, r2.ps, hps]
    · rw [r1.ps, r2.ps, hps]
    · rw [r1.bt, r2.bt]; exact cb
    · rw [r1.pc, r2.pc]; exact cp

/-- `Good` from the action equation and the result facts. -/
theorem good_of (A : SailM Unit) (F : BrSpec) (t u : NativeState) (h : A t = .ok () u) (r : RFacts F t u) :
    Good A F t u :=
  ⟨h, r.fr, r.mem, r.gpr, r.sp, r.z, r.ps, r.pc, r.bt, r.btt, r.npe, r.gic⟩

/-- Branch-action frame from the observation lemmas' frame. -/
theorem actFrame_of (t u : NativeState) (hF : Crypto.BcondCore.BrFrame t u) : ActFrameBr t u :=
  ⟨hF.bbool, hF.feat, by rw [hF.pstate], hF.btn, hF.b64, hF.b32, hF.bint, hF.ss, hF.it, hF.enc, hF.emu, hF.b128⟩

/-- Compose a pre-BranchTo frame with the BranchTo frame. -/
theorem frame_comp (t S u : NativeState) (h1 : ActFrameBr t S) (hF : Crypto.BcondCore.BrFrame S u) : ActFrameBr t u :=
  ⟨fun k hk => (hF.bbool k hk).trans (h1.bbool k hk), hF.feat.trans h1.feat, by rw [hF.pstate]; exact h1.pse,
    hF.btn.trans h1.btn, hF.b64.trans h1.b64, hF.b32.trans h1.b32, hF.bint.trans h1.bint, hF.ss.trans h1.ss,
    hF.it.trans h1.it, hF.enc.trans h1.enc, hF.emu.trans h1.emu, hF.b128.trans h1.b128⟩

/-- crux4 obligations hAM / hAG / hUM for R := Rg A F (every t; the fallback only writes masked fields). -/
theorem rg_npe (A : SailM Unit) (F : BrSpec) (t : NativeState) :
    ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs (Rg A F t).regs := (rfacts A F t).npe
theorem rg_gic (A : SailM Unit) (F : BrSpec) (t : NativeState) :
    (Rg A F t).regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending := (rfacts A F t).gic
theorem rg_um (A : SailM Unit) (F : BrSpec) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (t : NativeState) :
    ArmBridge.BoundaryV2.UnmappedSame m t (Rg A F t) := fun p _ _ => by rw [(rfacts A F t).mem]

#print axioms obligations
#print axioms rg_npe
#print axioms rg_um
end Crypto.CruxBrObl
