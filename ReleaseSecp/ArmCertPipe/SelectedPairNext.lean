-- The pair packet and its actual physical effect preserve the current SSA/profile invariant.
import NativeAccess.PairSelected
import ArmCertPipe.FDeploy
import RtG.ClassNextG
import ArmCertValue.PhysicalMemory
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk ArmCert.Translate.Model ArmBridge.Draft
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCertPipe.SelectedPairNext
open ArmCertValue NativeAccess
open ArmBridge.Boundary ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3

theorem of_packet {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop}
    {image : MemReloc.Image} {loadBase : MemReloc.Word} {base : BitVec 64}
    {offset : Nat → BitVec 64} {budget k : Nat} {view : Physical.BytePA} {regions : List Region}
    {σ0 : Sym} {inputs : List (BitVec 64)} {plan : List ArmCertValue.F.Step}
    {profile : AccessProfile} {x fin : NativeState}
    {us : List (HeapV2StepCerts.RegBind.Reg × HeapV2StepCerts.RegBind.Upd)}
    {D : Nat → Prop} {Pay : NativeState → NativeState → Prop}
    (inv : F.InvExtra spec config rows mapping m scope image loadBase base offset budget
      view regions σ0 inputs plan (fun _ s => ProfileAt profile s) k x)
    (room : k < plan.length)
    (compiles : (ArmCertValue.F.compileRun regions σ0 inputs.length plan).isSome = true)
    (packet : PairNext.Packet spec config rows mapping m scope image loadBase base offset budget k us D Pay x fin)
    (effect : ArmCertValue.F.Holds view regions plan[k] x fin) :
    F.InvExtra spec config rows mapping m scope image loadBase base offset budget
      view regions σ0 inputs plan (fun _ s => ProfileAt profile s) (k + 1) fin := by
  obtain ⟨pins,quiet,current,pc,debug,features,gic,closed,placed,branch,holds,written,pay,present,sysForward⟩ := packet
  obtain ⟨written,wo,separated,inD⟩ := written
  have sys := sysForward
  have agrees := F.agreesAt_succ room compiles inv.extra.1 effect
  have profileNext := PairTail.profile_of_sys inv.extra.2
    (ArmBridge.CruxGenGuarded.EntryBranchPins.sysEq2_symm _ _ sys)
  refine ⟨⟨⟨pins,features,debug,current,quiet,gic,pc⟩,closed,placed,branch⟩,?_,?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug,?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache,agrees,profileNext⟩
  · exact HeapV2StepCerts.RawFetch.raw_writes inv.raw wo separated
  · intro wr acc shape
    rw [hostHAFT_eq sys]
    exact inv.noUpd wr acc shape
  · rw [sys.feat]
    exact inv.feat

theorem class_next (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
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
    (inv : F.InvExtra spec config rows mapping m scope image loadBase base offset budget
      view regions σ0 inputs plan (fun _ s => ProfileAt profile s) k x)
    (tail : ClassTailXAt real w writes K x (next x) vus fl)
    (nextPlaced : next x = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      F.InvExtra spec config rows mapping m scope image loadBase base offset budget
        view regions σ0 inputs plan (fun _ s => ProfileAt profile s) (k + 1) fin ∧
      ArmCertValue.F.Holds view regions plan[k] x fin := by
  have hq : ArmCert.HookQuiet.V0.HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin,run,pins,quiet,current,pc,debug,features,gic,closed,placed,branch,vh,memory,sys,gcs⟩ :=
    RtG.entry_class_next_XG real spec config rows mapping w writes K x inv.v2.v1.pins (next x)
      (offset (k + 1)) vus fl tail inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned nextPlaced
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  have effect : ArmCertValue.F.Holds view regions plan[k] x fin := by
    rw [planEntry]
    exact ⟨vh,Physical.memV_nil_of_mem view regions x fin memory⟩
  have agrees := F.agreesAt_succ roomPlan compiles inv.extra.1 effect
  have profileNext := PairTail.profile_of_sys inv.extra.2
    (ArmBridge.CruxGenGuarded.EntryBranchPins.sysEq2_symm _ _ sys)
  refine ⟨fin,run,⟨⟨⟨pins,features,debug,current,quiet,gic,pc⟩,closed,placed,branch⟩,?_,?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug,?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache,agrees,profileNext⟩,effect⟩
  · rw [memory]; exact inv.raw
  · intro wr acc shape
    rw [hostHAFT_eq sys]
    exact inv.noUpd wr acc shape
  · rw [sys.feat]
    exact inv.feat

#print axioms class_next
#print axioms of_packet
end ArmCertPipe.SelectedPairNext
