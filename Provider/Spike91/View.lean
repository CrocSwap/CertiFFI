import Bridge.CruxGen
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace Spike91
open ArmBridge.Boundary ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1 ArmBridge.CruxCore

/-- Consumer view of a native state through a consumer map (no LNSym): GPRs, SP, PC, NZCV, DIT and
    the VA-addressed byte memory. -/
structure View where
  gpr : Fin 31 → BitVec 64
  sp : BitVec 64
  pc : BitVec 64
  n : BitVec 1
  z : BitVec 1
  c : BitVec 1
  v : BitVec 1
  dit : BitVec 1
  mem : BitVec 64 → BitVec 8

def view (m : ConsumerMap) (s : NativeState) : View :=
  ⟨fun i => s.regs.gpr[i.val], s.regs.SP_EL0, s.regs._PC, s.regs.PSTATE.N, s.regs.PSTATE.Z, s.regs.PSTATE.C,
    s.regs.PSTATE.V, s.regs.PSTATE.DIT, fun va => (s.mem[(m.pa va).toNat]?).getD 0#8⟩

/-- The extra crux export asked of (fin's gpr/SP/NZCV = the action result's). Until crux_gen_br
    exports it, summaries take it as a hypothesis on the crux witness. -/
structure FinExport (fin u : NativeState) : Prop where
  gpr : fin.regs.gpr = u.regs.gpr
  sp : fin.regs.SP_EL0 = u.regs.SP_EL0
  n : fin.regs.PSTATE.N = u.regs.PSTATE.N
  z : fin.regs.PSTATE.Z = u.regs.PSTATE.Z
  c : fin.regs.PSTATE.C = u.regs.PSTATE.C
  v : fin.regs.PSTATE.V = u.regs.PSTATE.V

/-- View of a state after an action result `u` that keeps gpr/SP/PSTATE/mem of `s`, with a new PC. -/
theorem view_pc (m : ConsumerMap) (s fin u : NativeState) (hx : FinExport fin u)
    (hg : u.regs.gpr = s.regs.gpr) (hsp : u.regs.SP_EL0 = s.regs.SP_EL0) (hps : u.regs.PSTATE = s.regs.PSTATE)
    (hmem : fin.mem = s.mem) (hdit : fin.regs.PSTATE.DIT = s.regs.PSTATE.DIT) (pc' : BitVec 64)
    (hpc : fin.regs._PC = pc') :
    view m fin = { view m s with pc := pc' } := by
  simp only [view, hx.gpr, hx.sp, hx.n, hx.z, hx.c, hx.v, hg, hsp, hps, hmem, hdit, hpc]


/-- General view lemma: fin's view from an action result u that rewrites gpr (to G), keeps SP/PSTATE/mem. -/
theorem view_gpr_pc (m : ConsumerMap) (s fin u : NativeState) (hx : FinExport fin u) (G : Vector (BitVec 64) 31)
    (hg : u.regs.gpr = G) (hsp : u.regs.SP_EL0 = s.regs.SP_EL0) (hps : u.regs.PSTATE = s.regs.PSTATE)
    (hmem : fin.mem = s.mem) (hdit : fin.regs.PSTATE.DIT = s.regs.PSTATE.DIT) (pc' : BitVec 64)
    (hpc : fin.regs._PC = pc') :
    view m fin = { view m s with gpr := fun i => G[i.val], pc := pc' } := by
  simp only [view, hx.gpr, hx.sp, hx.n, hx.z, hx.c, hx.v, hg, hsp, hps, hmem, hdit, hpc]

end Spike91
