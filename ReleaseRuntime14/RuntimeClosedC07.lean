import RuntimeClosed
import RuntimeGB10C2World
import R14GuardWitness.Inputs

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace ReleaseProfile.GB10.RuntimeClosed

open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.GB10 ReleaseProfile.GB10.Runtime

/-! ## c07 -/

noncomputable def world_c07 : RuntimeWorld where
  plan := ReleaseProfile.RuntimeGB10.WorldPlan.plan ReleaseProfile.RuntimeGB10.WorldCases.c07.db
  planKeys := Runtime.World.planKeys ReleaseProfile.RuntimeGB10.WorldCases.c07.db
  rows := ReleaseProfile.RuntimeGB10.World.permissionRows
  mapping := ReleaseProfile.RuntimeGB10.World.mapping
  table := (ArmCert.Translate.Model.rowsFootprint ReleaseProfile.RuntimeGB10.World.imageRows).byte
  sc := PipeR14.closureScope
  bytes := R14Sparse.imageBytes
  base := 0x400000#64
  ifunc := fun _ => 0#64
  p := ReleaseProfile.RuntimeGB10.WorldCases.c07.pins
  budget := PipeR14.plan_c07.length
  inputs := R14GuardWitness.c07.inputs
  data := Runtime.World.entryData ReleaseProfile.RuntimeGB10.WorldCases.c07.gprs R14Plan.entry_c07

theorem worldRegs_c07 (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    WorldRegs (world_c07.entry sem rho caller pcount).regs
      (controlWord rho.val caller.caller .TCR_EL2) (controlWord rho.val caller.caller .SCTLR_EL2) := by
  have hd : (world_c07.entry sem rho caller pcount).regs =
      sourceRegs rho caller { world_c07.data with PhysicalCount := pcount } := rfl
  rw [hd]
  refine ⟨rfl, rfl, by simp [sourceRegs, sourceBank64, isEntryData64, world_c07, Runtime.World.entryData],
    sourceRegs_bank64 rho caller _ .TCR_EL2, sourceRegs_bank64 rho caller _ .SCTLR_EL2,
    sourceRegs_feature rho caller _ 227 (by decide) false _ rfl,
    sourceRegs_feature rho caller _ 81 (by decide) true _ rfl,
    sourceRegs_feature rho caller _ 101 (by decide) true _ rfl, rfl, ?_, ?_, ?_⟩
  · bit1 .TCR_EL2 7 false
  · bit1 .SCTLR_EL2 12 true
  · bit1 .SCTLR_EL2 2 true

theorem closed_c07 {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho} {domain : QueryDomain}
    {spec : TopologyImageSpec domain} (w : WorldSpec spec)
    (hdom : ∀ q : AccessQuery, (∃ q0 ∈ ReleaseProfile.RuntimeGB10.World.queries, SamePage q0.va q.va) → domain q)
    (state : ArmCertWalk.State) {tcr sctlr : BitVec 64} (r : WorldRegs state.regs tcr sctlr) :
    ClosedMembershipAt spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.mapping
      (R14E17.consumerMap R14Plan.accesses_c07 R14Plan.codeWords_c07 R14Plan.entry_c07 ReleaseProfile.RuntimeGB10.WorldCases.c07.pins
        (0x400000#64 : BitVec 64).toNat ReleaseProfile.RuntimeGB10.World.mapping (ArmCert.Translate.Model.rowsFootprint ReleaseProfile.RuntimeGB10.World.imageRows).byte) state := by
  let rR : List (ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries (DataShape false)) := [rep_x1objRead w, rep_x0objRead w, rep_payloadRead w, rep_x19objRead w, rep_stackRead w]
  let rW : List (ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries (DataShape true)) := [rep_x1objWrite w, rep_x0objWrite w, rep_payloadWrite w, rep_x19objWrite w, rep_stackWrite w]
  let rF : List (ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries FetchShape) := [rep_fetch2b6000 w, rep_fetch2ba000 w, rep_fetch391000 w]
  have lR : ∀ x ∈ rR, x.level = 3 := by intro x hx; simp only [rR, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl
  have lW : ∀ x ∈ rW, x.level = 3 := by intro x hx; simp only [rW, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl
  have lF : ∀ x ∈ rF, x.level = 3 := by intro x hx; simp only [rF, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> rfl
  have hd : R14Plan.accesses_c07.all (fun a => if a.2.2.2
      then ClosedPages.accessOK spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.mapping rW state.regs (R14E17.dataVA ReleaseProfile.RuntimeGB10.WorldCases.c07.pins a.2.1) (a.2.2.1 : Int)
      else ClosedPages.accessOK spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.mapping rR state.regs (R14E17.dataVA ReleaseProfile.RuntimeGB10.WorldCases.c07.pins a.2.1) (a.2.2.1 : Int)) = true := by
    simp only [rR, rW, R14Plan.accesses_c07, List.all_cons, List.all_nil, Bool.and_true]
    all_goals acc_ok
  have hc : R14Plan.codeWords_c07.all (fun c => ClosedPages.accessOK spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.mapping rF state.regs
      (R14E17.codeVA (0x400000#64 : BitVec 64).toNat R14Plan.entry_c07 c.1) 4) = true := by
    simp only [rF, R14Plan.codeWords_c07, List.all_cons, List.all_nil, Bool.and_true]
    all_goals acc_ok
  refine R14E17.closed spec _ _ _ _ _ _ _ _ _ state ?_ ?_ ?_
  · intro va acc size permitted r
    rcases permitted with ⟨a, m, hva, hsize, shape⟩ | ⟨c, m, hva, hsize, shape⟩
    · have h := List.all_eq_true.1 hd a m; subst hva; subst hsize
      cases hw : a.2.2.2 <;> simp only [hw, Bool.false_eq_true, ite_false, ite_true] at h
      · exact hdom _ (ClosedPages.access_case_pages spec _ _ _ rR lR state.regs _ _ h state rfl).1
      · exact hdom _ (ClosedPages.access_case_pages spec _ _ _ rW lW state.regs _ _ h state rfl).1
    · subst hva; subst hsize
      exact hdom _ (ClosedPages.access_case_pages spec _ _ _ rF lF state.regs _ _ (List.all_eq_true.1 hc c m) state rfl).1
  · intro a m
    have h := List.all_eq_true.1 hd a m
    cases hw : a.2.2.2 <;> simp only [hw, Bool.false_eq_true, ite_false, ite_true] at h
    · obtain ⟨_, r, data, rshape, _, current⟩ := ClosedPages.access_case_pages spec _ _ _ rR lR state.regs _ _ h state rfl
      exact ⟨r, data, hw ▸ rshape, current⟩
    · obtain ⟨_, r, data, rshape, _, current⟩ := ClosedPages.access_case_pages spec _ _ _ rW lW state.regs _ _ h state rfl
      exact ⟨r, data, hw ▸ rshape, current⟩
  · intro c m
    obtain ⟨_, r, data, rshape, _, current⟩ := ClosedPages.access_case_pages spec _ _ _ rF lF state.regs _ _ (List.all_eq_true.1 hc c m) state rfl
    exact ⟨r, data, rshape, current⟩

#print axioms closed_c07

end ReleaseProfile.GB10.RuntimeClosed
