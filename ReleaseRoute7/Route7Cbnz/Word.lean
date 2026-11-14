-- Vendored from loops ws/LoopNative/Cbnz64/Word.lean (gen/tails.py output), renamed to Route7Cbnz.* (route 7 unit 3).
import Bridge.BvField
open BitVec
namespace Route7Cbnz.Dispatch
set_option autoImplicit false
def word (sf : BitVec 1) (fixed : BitVec 6) (op : BitVec 1) (imm19 : BitVec 19) (Rt : BitVec 5) : BitVec 32 :=
  sf ++ fixed ++ op ++ imm19 ++ Rt
def selected (Rt : BitVec 5) (imm19 : BitVec 19) : BitVec 32 := word 1#1 26#6 1#1 imm19 Rt
end Route7Cbnz.Dispatch
