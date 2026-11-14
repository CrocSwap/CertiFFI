-- Memory (runtime14 synthetic deployment, part B; layout): closure code bytes as NativeSourceInit plan rows,
-- identity+offset onto PA 0x80100000 + image offset (load base 0x400000), as in heap-v2.
import R14LoaderSynth.CodeBytes
import NativeSourceInit.PhysicalPlan
set_option autoImplicit false
namespace R14LoaderSynth

def codePA (o : Nat) : Nat := 0x80100000 + o

def codePlan : NativeSourceInit.Plan := codeBytes.map fun r => (codePA r.1, BitVec.ofNat 8 r.2)

/-- Code rows sit at distinct PAs inside [0x80100000 + 0x2b6000, 0x80100000 + 0x392000), away from the data
pages (0x80130000..0x80133000) and the stack page (0x801ff000..0x80200000). -/
theorem codePlan_range : codePlan.all (fun r => decide (0x803b6000 ≤ r.1 ∧ r.1 < 0x80492000)) = true := by decide +kernel
theorem codePlan_nodup : (codePlan.map (·.1)).Nodup := by decide +kernel

end R14LoaderSynth
