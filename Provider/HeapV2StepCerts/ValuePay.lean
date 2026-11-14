-- Memory: byte-class payload relations for the memory rich steps (STP / LDP reuse
-- RtSaved.MemFacts.StpPay and RtSaved3.MemFacts2.LdpPay2).
import HeapV2StepCerts.MemHolds
import ArmCertTranslateModel.HeapV2E17Table
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
namespace HeapV2StepCerts.ValuePay
open ArmBridge.Draft HeapV2StepCerts.RegBind

/-- LDRB payload: X[Rt] := ldrbVal of whatever byte sits at the access's PA in `f`. -/
def PayLdrb (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (e : Nat × Nat × Int × Nat × Bool)
    (Rt : BitVec 5) (f fin : NativeState) : Prop :=
  ∀ n, mapping (HeapV2E17.dataVA p e) = some n → ∀ b, f.mem[n]? = some b →
    fin.regs.gpr[(rk Rt).val] = ArmCertMem.LdrbEval.ldrbVal b

/-- STRB payload: the byte at the access's PA is the low byte of X[Rt] of `f`. -/
def PayStrb (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (e : Nat × Nat × Int × Nat × Bool)
    (Rt : BitVec 5) (f fin : NativeState) : Prop :=
  ∀ n, mapping (HeapV2E17.dataVA p e) = some n → fin.mem[n]? = some ((f.regs.gpr[(rk Rt).val]).setWidth 8)

theorem PayLdrb.transport {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {e : Nat × Nat × Int × Nat × Bool}
    {Rt : BitVec 5} {f s fin : NativeState} (mem : f.mem = s.mem) (h : PayLdrb p mapping e Rt f fin) :
    PayLdrb p mapping e Rt s fin :=
  fun n hn b hb => h n hn b (by rw [mem]; exact hb)

theorem PayStrb.transport {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {e : Nat × Nat × Int × Nat × Bool}
    {Rt : BitVec 5} {f s fin : NativeState} (gpr : f.regs.gpr = s.regs.gpr) (h : PayStrb p mapping e Rt f fin) :
    PayStrb p mapping e Rt s fin :=
  fun n hn => by rw [← gpr]; exact h n hn

end HeapV2StepCerts.ValuePay
