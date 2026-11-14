-- Actual scalar class continuation with current SSA, tag controls and branch pins.
import TranslateSpan.ClassMTE2
import TranslateSpan.BranchMTE2
import ArmCertPipe.FDeploy
import ArmCertValue.PhysicalMemory

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCertValue ArmCertPipe NativeAccess
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.CurrentMTE2

structure Inv {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (profile : AccessProfile)
    (view : Physical.BytePA) (regions : List Region) (σ0 : Sym) (inputs : List (BitVec 64))
    (plan : List ArmCertValue.F.Step) (k : Nat) (s : NativeState) : Prop where
  core : Core spec config rows mapping m scope image loadBase base offset budget profile k s
  branch : BranchMTE2.Pins s
  agrees : ArmCertPipe.F.AgreesAt view regions σ0 inputs plan k s

theorem post_of_sys {r r' : Regs} (sys : SysEq2 r r') (post : MemM1.MemReadD.PostRegs r) :
    MemM1.MemReadD.PostRegs r' :=
  ⟨sys.spe ▸ post.spe, sys.el ▸ post.el0, sys.nrw ▸ post.nrw, sys.feat ▸ post.noRME,
    sys.feat ▸ post.vhe, sys.feat ▸ post.aa64el0, sys.scr ▸ post.ns, sys.hcr ▸ post.e2h,
    sys.hcr ▸ post.tge, sys.sctlr ▸ post.e0e⟩

theorem profile_of_sys {x fin : NativeState} {profile : AccessProfile}
    (sys : SysEq2 x.regs fin.regs) (h : ProfileAt profile x) : ProfileAt profile fin :=
  ⟨sys.feat ▸ h.lse2,sys.feat ▸ h.lrcpc3,
    ⟨sys.el ▸ h.host.el,sys.nrw ▸ h.host.nrw,sys.feat ▸ h.host.aa64,
      sys.feat ▸ h.host.rme,sys.feat ▸ h.host.vhe,sys.scr ▸ h.host.ns,
      sys.hcr ▸ h.host.e2h,sys.hcr ▸ h.host.tge⟩,sys.sctlr ▸ h.alignment_disabled⟩

theorem class_next (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (view : Physical.BytePA) (regions : List Region) (σ0 : Sym) (inputs : List (BitVec 64))
    (plan : List ArmCertValue.F.Step) (profile : AccessProfile) (k : Nat)
    (room : k < budget) (roomPlan : k < plan.length)
    (compiles : (ArmCertValue.F.compileRun regions σ0 inputs.length plan).isSome = true)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (next : NativeState → BitVec 64)
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option VUpd))
    (fl : Option (VUpd × VUpd × VUpd × VUpd))
    (planEntry : plan[k] = .legacy ⟨vus,fl,[]⟩)
    (x : NativeState)
    (inv : Inv spec config rows mapping m scope image loadBase base offset budget profile
      view regions σ0 inputs plan k x)
    (tail : ClassTailXAt real w writes K x (next x) vus fl)
    (nextPlaced : next x = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      Inv spec config rows mapping m scope image loadBase base offset budget profile
        view regions σ0 inputs plan (k + 1) fin ∧
      ArmCertValue.F.Holds view regions plan[k] x fin := by
  have hq : ArmCert.HookQuiet.V0.HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.core.v1.quiet
  obtain ⟨fin,run,pins,quiet,current,pc,debug,features,gic,closed,placed,vh,memory,sys,_gcs,br,tco⟩ :=
    ClassMTE2.entry_class_next real spec config rows mapping w writes K x inv.core.v1.pins (next x)
      (offset (k + 1)) vus fl tail inv.core.v1.gic inv.core.v1.features
      inv.core.v1.debug (budget - (k + 1)) hq base (offset k) inv.core.v1.pc page aligned nextPlaced
      inv.core.v1.current m inv.core.closed scope image loadBase inv.core.placed separated
      inv.core.raw inv.core.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  have effect : ArmCertValue.F.Holds view regions plan[k] x fin := by
    rw [planEntry]
    exact ⟨vh,Physical.memV_nil_of_mem view regions x fin memory⟩
  have agrees := ArmCertPipe.F.agreesAt_succ roomPlan compiles inv.agrees effect
  have profileNext := profile_of_sys sys inv.core.profileAt
  refine ⟨fin,run,⟨⟨⟨pins,features,debug,current,quiet,gic,pc⟩,closed,placed,?_,?_,
    post_of_sys sys inv.core.post,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.core.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.core.debug,?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.core.dcache,profileNext,?_,tco.trans inv.core.tco⟩,
    BranchMTE2.pins_step x fin inv.branch sys pins br,agrees⟩,effect⟩
  · rw [memory]; exact inv.core.raw
  · intro wr acc shape
    rw [hostHAFT_eq sys]
    exact inv.core.noUpd wr acc shape
  · rw [sys.feat]
    exact inv.core.feat
  · rw [sys.feat]
    exact inv.core.mte2

#print axioms post_of_sys
#print axioms profile_of_sys
#print axioms class_next
end TranslateSpan.CurrentMTE2
