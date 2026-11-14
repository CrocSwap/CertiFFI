-- (heap-v2 premise B, RunPremisesB split): the shim's class tails at steps 1 (sub sp, sp, #16)
-- and 366 (add sp, sp, #16) as RegValE.ClassTailVAt at the next PC, invariant-indexed. They are Memory's
-- HeapV2StepCerts.RootVE.{SubSp64,AddSpRestore}_tailV at imm12 = 16 (heap-v2 body classes; both adapter Profiles are
-- empty) via ClassTailV.at; the update facts hw / sub / add / keep are by rfl on the concrete writes / us.
import NativeShimFetch.Inv
import HeapV2StepCerts.RootTailVE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded
set_option autoImplicit false
namespace NativeShimTails
open ArmBridge.CruxGenGuarded.Release (shimMap)
open HeapV2StepCerts

abbrev writes1 : NativeEntry.Effects.Writes := NativeEntryBodyAdapters.SubSp64.writes
abbrev K1 : Int := 20
abbrev us1 : List (RegBind.Reg × RegBind.Upd) := [(.sp, .set .sp (-((16#12 : BitVec 12).toNat : Int)))]
abbrev writes8 : NativeEntry.Effects.Writes := NativeEntryBodyAdapters.AddSpRestore.writes
abbrev K8 : Int := 18
abbrev us8 : List (RegBind.Reg × RegBind.Upd) := [(.sp, .set .sp ((16#12 : BitVec 12).toNat : Int))]

theorem noEret1 : (Sail.BitVec.extractLsb NativeShimFetch.w1 31 12 == 879088#20) = false := by decide
theorem noEret8 : (Sail.BitVec.extractLsb NativeShimFetch.w8 31 12 == 879088#20) = false := by decide

variable {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig} {rows : List PermissionRow}
  {mapping : BitVec 64 → Option Nat} {scope : Nat → Prop} {image : MemReloc.Image} {loadBase : MemReloc.Word}
  {base : BitVec 64} {offS : Nat → BitVec 64} {budget : Nat} {pins : HeapV2E17.Pins}

theorem tail1 (real : Type) [Sail.SailReal real] :
    ∀ x, RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 1 x →
      RegValE.ClassTailVAt real NativeShimFetch.w1 writes1 K1 x (x.regs._PC + 4#64) us1 :=
  fun x _ => RegValE.ClassTailV.at (RootVE.SubSp64.SubSp64_tailV real x 16#12 noEret1 ⟨⟩)

theorem tail8 (real : Type) [Sail.SailReal real] :
    ∀ x, RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 366 x →
      RegValE.ClassTailVAt real NativeShimFetch.w8 writes8 K8 x (x.regs._PC + 4#64) us8 :=
  fun x _ => RegValE.ClassTailV.at (RootVE.AddSpRestore.AddSpRestore_tailV real x 16#12 noEret8 ⟨⟩)

theorem hw1 : writes1.dit = false := by decide
theorem hw8 : writes8.dit = false := by decide
theorem sub1 : RegBind.updOf us1 .sp = .set .sp (-16) := by decide
theorem add8 : RegBind.updOf us8 .sp = .set .sp 16 := by decide
theorem keep1all : ∀ i : Fin 31, RegBind.updOf us1 (.x i) = .keep := by decide
theorem keep8all : ∀ i : Fin 31, RegBind.updOf us8 (.x i) = .keep := by decide

#print axioms tail1
#print axioms tail8
#print axioms hw1
#print axioms sub1
#print axioms keep1all
end NativeShimTails
