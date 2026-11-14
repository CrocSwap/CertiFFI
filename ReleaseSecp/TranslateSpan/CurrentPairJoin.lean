-- The concrete native pair route supplies same-successor facts. The invariant,
-- table/code memory and SSA are assembled here from those exact effects.
import TranslateSpan.CurrentClass
import TranslateSpan.StaticLayout

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCertValue NativeAccess
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.CurrentMTE2

/-- The finite checked output footprint is physically separate from table bytes. -/
theorem output_separated (view : Physical.BytePA) (r : Region) (bytes : Nat) (f : Footprint)
    (checked : StaticLayout.checkOutput view r bytes f = true) :
    Separated f.byte (fun pa => pa ∈ StaticLayout.outputPAs view r bytes) := by
  intro pa table written
  obtain ⟨j,member,mapped⟩ := List.mem_filterMap.mp written
  have h := List.all_eq_true.mp checked j member
  simp [mapped,(StaticLayout.footprintByte_true _ _).mpr table] at h

/-- Transport the actual SSA and fixed-entry control obligations across a
native pair result whose write frame and system register frame have been proved. -/
theorem of_pair_effect {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop}
    {image : MemReloc.Image} {loadBase base : BitVec 64} {offset : Nat → BitVec 64}
    {budget k : Nat} {profile : AccessProfile} {view : Physical.BytePA} {regions : List Region}
    {σ0 : Sym} {inputs : List (BitVec 64)} {plan : List ArmCertValue.F.Step}
    {x fin : NativeState} {D : Nat → Prop}
    (inv : Inv spec config rows mapping m scope image loadBase base offset budget profile view regions σ0 inputs plan k x)
    (room : k < plan.length)
    (compiles : (ArmCertValue.F.compileRun regions σ0 inputs.length plan).isSome = true)
    (next : ChainInv spec config rows base offset budget (k + 1) fin)
    (closed : ClosedMembershipAt spec config rows mapping m (beforeFetchState fin))
    (sys : SysEq2 x.regs fin.regs) (br : BrSysEq x.regs fin.regs)
    (tco : fin.regs.PSTATE.TCO = x.regs.PSTATE.TCO)
    (writes : WritesOnly D (fun pa => x.mem[pa]?) (fun pa => fin.mem[pa]?))
    (tableD : Separated (rowsFootprint spec.imageRows).byte D)
    (codeD : ImageTableSeparated scope loadBase mapping D)
    (effect : ArmCertValue.F.Holds view regions plan[k] x fin) :
    Inv spec config rows mapping m scope image loadBase base offset budget profile
      view regions σ0 inputs plan (k + 1) fin := by
  have agrees := ArmCertPipe.F.agreesAt_succ room compiles inv.agrees effect
  have placed := MemReloc.imageOn_frame inv.core.placed (scope_memory_eq_of_writes_only codeD writes)
  refine ⟨⟨next,closed,placed,HeapV2StepCerts.RawFetch.raw_writes inv.core.raw writes tableD,?_,
    post_of_sys sys inv.core.post,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.core.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.core.debug,?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.core.dcache,profile_of_sys sys inv.core.profileAt,?_,
    tco.trans inv.core.tco⟩, BranchMTE2.pins_step x fin inv.branch sys next.pins br, agrees⟩
  · intro wr acc shape
    rw [hostHAFT_eq sys]
    exact inv.core.noUpd wr acc shape
  · rw [sys.feat]; exact inv.core.feat
  · rw [sys.feat]; exact inv.core.mte2

#print axioms output_separated
#print axioms of_pair_effect
end TranslateSpan.CurrentMTE2
