import ArmFull
open ArmFull
namespace ArmBridge.PSRest
/-- The 28 non-NZCV fields of a ProcState. -/
def rest (p : ProcState) := (p.D, p.A, p.I, p.F, p.EXLOCK, p.PAN, p.UAO, p.DIT, p.TCO, p.PM, p.PPEND, p.BTYPE, p.ZA, p.SM, p.ALLINT, p.SS, p.IL, p.EL, p.nRW, p.SP, p.Q, p.GE, p.SSBS, p.IT, p.J, p.T, p.E, p.M)
theorem erase_of_rest (u t : ProcState) (h : (u.D, u.A, u.I, u.F, u.EXLOCK, u.PAN, u.UAO, u.DIT, u.TCO, u.PM, u.PPEND, u.BTYPE, u.ZA, u.SM, u.ALLINT, u.SS, u.IL, u.EL, u.nRW, u.SP, u.Q, u.GE, u.SSBS, u.IT, u.J, u.T, u.E, u.M) = (t.D, t.A, t.I, t.F, t.EXLOCK, t.PAN, t.UAO, t.DIT, t.TCO, t.PM, t.PPEND, t.BTYPE, t.ZA, t.SM, t.ALLINT, t.SS, t.IL, t.EL, t.nRW, t.SP, t.Q, t.GE, t.SSBS, t.IT, t.J, t.T, t.E, t.M)) :
    ({ u with N := 0#1, Z := 0#1, C := 0#1, V := 0#1 } : ProcState) = { t with N := 0#1, Z := 0#1, C := 0#1, V := 0#1 } := by
  cases u; cases t
  simp only [Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := h
  subst h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27
  rfl
#print axioms erase_of_rest
end ArmBridge.PSRest
