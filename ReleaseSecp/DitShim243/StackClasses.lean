-- Concrete stack-update words and bindings, source-lifted from NativeShimTails.Inv.
import HeapV2StepCerts.RootTailVE
open Sail ArmFull HeapV2StepCerts
set_option autoImplicit false
namespace DitShim243.StackClasses

def w1 : BitVec 32 := NativeEntryBodyDispatch.SubSp64.selected 16#12
def w8 : BitVec 32 := NativeEntryBodyDispatch.AddSpRestore.selected 16#12
abbrev writes1 : NativeEntry.Effects.Writes := NativeEntryBodyAdapters.SubSp64.writes
abbrev K1 : Int := 20
abbrev us1 : List (RegBind.Reg × RegBind.Upd) := [(.sp, .set .sp (-((16#12 : BitVec 12).toNat : Int)))]
abbrev writes8 : NativeEntry.Effects.Writes := NativeEntryBodyAdapters.AddSpRestore.writes
abbrev K8 : Int := 18
abbrev us8 : List (RegBind.Reg × RegBind.Upd) := [(.sp, .set .sp ((16#12 : BitVec 12).toNat : Int))]
theorem noEret1 : (Sail.BitVec.extractLsb w1 31 12 == 879088#20) = false := by decide
theorem noEret8 : (Sail.BitVec.extractLsb w8 31 12 == 879088#20) = false := by decide
theorem hw1 : writes1.dit = false := by decide
theorem hw8 : writes8.dit = false := by decide
theorem sub1 : RegBind.updOf us1 .sp = .set .sp (-16) := by decide
theorem add8 : RegBind.updOf us8 .sp = .set .sp 16 := by decide
theorem keep1all : ∀ i : Fin 31, RegBind.updOf us1 (.x i) = .keep := by decide
theorem keep8all : ∀ i : Fin 31, RegBind.updOf us8 (.x i) = .keep := by decide
end DitShim243.StackClasses
