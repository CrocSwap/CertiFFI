-- The concrete native pair route supplies same-successor facts. The invariant,
-- table/code memory and SSA are assembled here from those exact effects.
import TranslateSpan.DefaultClass
import TranslateSpan.StaticLayout

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCertValue ArmCertPipe NativeAccess NativeMteTagCheck
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.DefaultMTE2

/-- Transport the actual SSA and fixed-entry control obligations across a
native pair result whose write frame and system register frame have been proved. -/
theorem of_pair_effect {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop}
    {image : MemReloc.Image} {loadBase base : BitVec 64} {offset : Nat → BitVec 64}
    {budget k : Nat} {profile : AccessProfile} {view : Physical.BytePA} {regions : List Region}
    {σ0 : Sym} {inputs : List (BitVec 64)} {language : ValuePlan.Language}
    {plan : List (ValuePlan.Step language)} {catalogue : ControlCatalogue}
    {entry : NativeState} {capacity : Nat} {drawsBefore : Nat → Nat}
    {x fin : NativeState} {D : Nat → Prop}
    (inv : Inv spec config rows mapping m scope image loadBase base offset budget profile catalogue
      language view regions σ0 inputs plan entry capacity drawsBefore k x)
    (room : k < plan.length)
    (compiles : (ValuePlan.compileRun language regions σ0 inputs.length plan).isSome = true)
    (next : ChainInv spec config rows base offset budget (k + 1) fin)
    (closed : ClosedMembershipAt spec config rows mapping m (beforeFetchState fin))
    (sys : SysEq2 x.regs fin.regs) (br : BrSysEq x.regs fin.regs)
    (tco : fin.regs.PSTATE.TCO = x.regs.PSTATE.TCO)
    (writes : WritesOnly D (fun pa => x.mem[pa]?) (fun pa => fin.mem[pa]?))
    (tableD : Separated (rowsFootprint spec.imageRows).byte D)
    (codeD : ImageTableSeparated scope loadBase mapping D)
    (effect : ValuePlan.Holds language view regions plan[k] x fin)
    (cost : Nat) (delta : ∃ draws, ChoiceDelta x fin draws ∧ draws ≤ cost)
    (drawBound : drawsBefore k + cost ≤ drawsBefore (k + 1)) :
    Inv spec config rows mapping m scope image loadBase base offset budget profile catalogue
      language view regions σ0 inputs plan entry capacity drawsBefore (k + 1) fin := by
  have agrees := ValuePlan.advance language view regions σ0 inputs plan k x fin room compiles inv.agrees effect
  have placed := MemReloc.imageOn_frame inv.core.placed (scope_memory_eq_of_writes_only codeD writes)
  refine ⟨⟨next,closed,placed,HeapV2StepCerts.RawFetch.raw_writes inv.core.raw writes tableD,?_,
    CurrentMTE2.post_of_sys sys inv.core.post,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.core.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.core.debug,?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.core.dcache,CurrentMTE2.profile_of_sys sys inv.core.profileAt,
    controls_of_sys inv.core.controls sys tco⟩, BranchMTE2.pins_step x fin inv.branch sys next.pins br, agrees,inv.statusRows,
    bounded_trace_next entry x fin (drawsBefore k) (drawsBefore (k + 1)) cost inv.trace delta drawBound⟩
  · intro wr acc shape
    rw [hostHAFT_eq sys]
    exact inv.core.noUpd wr acc shape
  · rw [sys.feat]; exact inv.core.feat

#print axioms of_pair_effect
end TranslateSpan.DefaultMTE2
