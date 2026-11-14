import BridgeV2.ConsumerMap
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxL
open ArmCert.Premises.TranslationAgreesV1

theorem pre_trans {a b c : Regs} (h1 : ProjRegsEq a b) (h2 : ProjRegsEq b c) : ProjRegsEq a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7, b8.trans a8,
    b9.trans a9, b10.trans a10, b11.trans a11, b12.trans a12, b13.trans a13, b14.trans a14, b15.trans a15,
    b16.trans a16, b17.trans a17, b18.trans a18⟩

theorem pre_symm {a b : Regs} (h : ProjRegsEq a b) : ProjRegsEq b a := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := h
  exact ⟨a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm, a10.symm, a11.symm,
    a12.symm, a13.symm, a14.symm, a15.symm, a16.symm, a17.symm, a18.symm⟩

theorem pre_of_fields {r r' : Regs} (h1 : r'.gpr = r.gpr) (h2 : r'.SP_EL0 = r.SP_EL0) (h3 : r'._Z = r._Z)
    (h4 : r'._PC = r._PC) (h5 : r'.PSTATE = r.PSTATE) (h6 : r'.bank_BitVec_64 = r.bank_BitVec_64) :
    ProjRegsEq r r' := by
  unfold ProjRegsEq
  simp only [Register.TPIDR_EL0, Register.TPIDRRO_EL0, Register.DCZID_EL0, Register.MIDR_EL1, Register.ID_AA64ISAR1_EL1,
    Register.ID_AA64ISAR2_EL1, Register.ID_AA64MMFR1_EL1, Register.TCR_EL1, Register.TCR_EL2, Register.HCR_EL2,
    Regs.ref_BitVec_64, h1, h2, h3, h4, h5, h6]
  simp

#print axioms pre_trans
#print axioms pre_of_fields
end ArmBridge.CruxL
