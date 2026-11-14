-- LNSym-free: Sail-side content only; the LNSym ArmInst decode theorem moved to CruxMem.LdstUoffDecodeLNSym.
open BitVec
namespace ArmCertMem.LdstUoff

/-- The LDR/STR (immediate, unsigned offset, GPR) instruction word built from its fields:
    size:2 111 V=0 01 opc:2 imm12:12 Rn:5 Rt:5. -/
def ldstUoffWord (size : BitVec 2) (opc : BitVec 2) (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) : BitVec 32 :=
  size ++ 7#3 ++ 0#1 ++ 1#2 ++ opc ++ imm12 ++ Rn ++ Rt


end ArmCertMem.LdstUoff
