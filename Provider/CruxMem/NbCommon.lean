import CruxMem.UoffCommon
import Bridge.CruxGenNB
import MemM1.MemWriteD1
import BridgeV2.BoundaryV2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmCertMem.NbCommon
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2

/-! Shared helper for the crux_gen_nb instances (hUM): a store of `k` bytes at `m.pa va`, `va` permitted for `k`
bytes, only touches mapped PAs (MapOK contiguity), so every unmapped byte is unchanged. -/

theorem um_wfold {m : ConsumerMap} (hmap : MapOK m) (va : BitVec 64) (acc : AccessDescriptor) (k : Nat)
    (hp : m.permitted va acc true (k : Int)) (mem : Std.ExtHashMap Nat (BitVec 8)) (g : Nat → BitVec 8) (q : Nat)
    (hq : ¬ MappedPA m q) : (MemM1.MemWriteD1.wfold mem (m.pa va).toNat k g).get? q = mem.get? q := by
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.get?_eq_getElem?, MemM1.MemWriteD1.wfold_get]
  rw [if_neg]
  rintro ⟨h1, h2⟩
  apply hq
  refine ⟨va + BitVec.ofNat 64 (q - (m.pa va).toNat), ⟨va, acc, true, (k : Int), q - (m.pa va).toNat, hp, by omega, rfl⟩, ?_⟩
  rw [hmap.contiguous va acc true _ _ hp (by omega)]
  omega

#print axioms um_wfold
end ArmCertMem.NbCommon
