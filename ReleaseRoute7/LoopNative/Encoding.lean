import LoopNative.Cbz64.Dispatch
import LoopNative.Cbnz64.Dispatch
import NativeEntryBodyDispatch.LdrbUoff
import NativeEntryBodyDispatch.StrbUoff
open Sail
namespace LoopNative.Encoding
set_option autoImplicit false
set_option maxHeartbeats 100000

theorem Cbz64_noEret (Rt : BitVec 5) (imm19 : BitVec 19) :
    (Sail.BitVec.extractLsb (LoopNative.Cbz64.Dispatch.selected Rt imm19) 31 12 == 879088#20) = false := by
  have ne : Sail.BitVec.extractLsb (LoopNative.Cbz64.Dispatch.selected Rt imm19) 31 12 ≠ 879088#20 := by
    intro h
    have bit := congrArg (fun v : BitVec 20 => v.getLsbD 18) h
    simp only [LoopNative.Cbz64.Dispatch.selected, NativeEntryBodyDispatch.Cbz.selected, NativeEntryBodyDispatch.Cbz.word, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] at bit
    simp at bit
  simpa using ne
#print axioms Cbz64_noEret


theorem Cbnz64_noEret (Rt : BitVec 5) (imm19 : BitVec 19) :
    (Sail.BitVec.extractLsb (LoopNative.Cbnz64.Dispatch.selected Rt imm19) 31 12 == 879088#20) = false := by
  have ne : Sail.BitVec.extractLsb (LoopNative.Cbnz64.Dispatch.selected Rt imm19) 31 12 ≠ 879088#20 := by
    intro h
    have bit := congrArg (fun v : BitVec 20 => v.getLsbD 18) h
    simp only [LoopNative.Cbnz64.Dispatch.selected, LoopNative.Cbnz64.Dispatch.word, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] at bit
    simp at bit
  simpa using ne
#print axioms Cbnz64_noEret


theorem LdrbU_noEret (Rt Rn : BitVec 5) (imm12 : BitVec 12) :
    (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.LdrbUoff.selected Rt Rn imm12) 31 12 == 879088#20) = false := by
  have ne : Sail.BitVec.extractLsb (NativeEntryBodyDispatch.LdrbUoff.selected Rt Rn imm12) 31 12 ≠ 879088#20 := by
    intro h
    have bit := congrArg (fun v : BitVec 20 => v.getLsbD 18) h
    simp only [NativeEntryBodyDispatch.LdrbUoff.selected, NativeEntryBodyDispatch.LdrbUoff.word, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] at bit
    simp at bit
  simpa using ne
#print axioms LdrbU_noEret


theorem StrbU_noEret (Rt Rn : BitVec 5) (imm12 : BitVec 12) :
    (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrbUoff.selected Rt Rn imm12) 31 12 == 879088#20) = false := by
  have ne : Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrbUoff.selected Rt Rn imm12) 31 12 ≠ 879088#20 := by
    intro h
    have bit := congrArg (fun v : BitVec 20 => v.getLsbD 18) h
    simp only [NativeEntryBodyDispatch.StrbUoff.selected, NativeEntryBodyDispatch.StrbUoff.word, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] at bit
    simp at bit
  simpa using ne
#print axioms StrbU_noEret

end LoopNative.Encoding
