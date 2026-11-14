-- Close the actual prepared data query at its real preparation successor.
import ArmCertTranslateModel.ClosedTable
import NativeMteTagCheck.Transport
import TagCheckFrames.Translation
import NativeAccess.Current

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open NativeAccess NativeAccess.Trace S1Normality
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.DefaultMTE2

theorem translation_from_closed {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (offset : Nat) (va : BitVec 64) (n : Nat) (aligned pair write : Bool) (acc : AccessDescriptor)
    (s : NativeMteTagCheck.State) (shape : DataShape write acc)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (controls : NativeMteTagCheck.DefaultAt catalogue s)
    (permitted : m.permitted va acc aligned (n : Int))
    (closed : ClosedMembershipAt spec config rows mapping m s)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (post : MemM1.MemReadD.PostRegs s.regs)
    (debug : ExistingE11DebugAt s.regs) (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping va = some pa.toNat)
    (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : ∀ wr a, DataShape wr a →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} a spec.imageRows = true)
    (prepared : NativeMteTagCheck.State) (frame : NativeMteTagCheck.StatusTrace.TraceFrame s prepared) :
    ∃ ad t, AArch64_TranslateAddress va acc aligned (n : Int) prepared = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      NormalWB ad ∧ ad.vaddress = va ∧ t.regs = s.regs ∧ t.mem = s.mem ∧
      (∃ W, t.events = prepared.events ++ W) ∧ MemM1.MemReadD.PostRegs t.regs ∧ NativeMteTagCheck.DefaultAt catalogue t ∧
      NativeMteTagCheck.ChoiceDelta s t 0 := by
  obtain ⟨⟨qva,⟨qacc,qal⟩,qn⟩,hva,hacc,hal,hn,member,data,access⟩ :=
    closed va acc aligned (n : Int) permitted
  simp only at hva hacc hal hn
  subst qva qacc qal qn
  have notFetch : ((acc : AccessDescriptor).acctype == .AccessType_IFETCH) = false := by
    rw [shape.acctype]; rfl
  obtain ⟨ad,t,run,nf,paddr,wb,address,regs,mem,ev⟩ :=
    NativeAccess.Current.translation_facts spec config rows mapping
      ⟨offset,va,n,acc,aligned,pair⟩ s member data current access
      mode post.aa64el0 debug post.spe notFetch dcache pa mapped raw (noUpd _ _ shape) prepared (NativeMteTagCheck.StatusTrace.to_frame frame)
  have stepDelta := TagCheckFrames.translation_preserves va acc aligned (n : Int) prepared ad t run
  have delta : NativeMteTagCheck.ChoiceDelta s t 0 := by
    simpa only [Nat.zero_add] using NativeMteTagCheck.choice_delta_trans frame.2.2.2 stepDelta
  refine ⟨ad,t,run,nf,paddr,wb,address,regs,mem,ev,by rw [regs]; exact post,?_,delta⟩
  rcases controls with ⟨⟨el,nrw,aa64,rme,vhe,ns,e2h,tge⟩,mte2,tco,tcf0,preparation⟩
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  all_goals (try unfold NativeMteTagCheck.PreparationAt) <;> rw [regs] <;> assumption

theorem have_tme_preserves : TagCheckFrames.Preserves (HaveTME ()) := by
  intro s value after run
  cases run
  exact NativeMteTagCheck.choice_delta_refl s

theorem status_after_tme (s : NativeMteTagCheck.State) (allowed : NativeMteTagCheck.TagStatusOK s) :
    ∀ value after, HaveTME () s = .ok value after → NativeMteTagCheck.TagStatusOK after := by
  intro value after run
  exact NativeMteTagCheck.tag_status_transport (have_tme_preserves s value after run) allowed

theorem shape_of_prepared (write : Bool) (acc prepared : AccessDescriptor)
    (shape : DataShape write acc)
    (same : prepared = { acc with tagchecked := prepared.tagchecked }) : DataShape write prepared := by
  rw [same]
  exact ⟨shape.acctype,shape.el,shape.ss,shape.read,shape.write,shape.tagaccess,
    shape.transactional,shape.nonfault,shape.contiguous,shape.firstfault,shape.first,shape.ls64⟩

theorem translation_from_checked_bytes {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (offset : Nat) (va : BitVec 64) (n : Nat) (aligned pair write : Bool) (acc : AccessDescriptor)
    (s : NativeMteTagCheck.State) (shape : DataShape write acc)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (controls : NativeMteTagCheck.DefaultAt catalogue s)
    (permitted : ∀ a, DataShape write a → m.permitted va a aligned (n : Int))
    (closed : ClosedMembershipAt spec config rows mapping m s)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (post : MemM1.MemReadD.PostRegs s.regs)
    (debug : ExistingE11DebugAt s.regs) (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping va = some pa.toNat)
    (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : ∀ wr a, DataShape wr a →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} a spec.imageRows = true)
    (data : BitVec (n * 8))
    (bytes : ∀ i < n, s.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8))
    (allowed : NativeMteTagCheck.TagStatusOK s)
    (prepared : AccessDescriptor) (u : NativeMteTagCheck.State)
    (same : prepared = { acc with tagchecked := prepared.tagchecked })
    (frame : NativeMteTagCheck.StatusTrace.TraceFrame s u) :
    ∃ ad t, AArch64_TranslateAddress va prepared aligned (n : Int) u = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      NormalWB ad ∧ ad.vaddress = va ∧ t.regs = s.regs ∧ t.mem = s.mem ∧
      (∃ W, t.events = u.events ++ W) ∧ MemM1.MemReadD.PostRegs t.regs ∧
      NativeMteTagCheck.DefaultAt catalogue t ∧ NativeMteTagCheck.ChoiceDelta s t 0 ∧
      (∀ value after, HaveTME () t = .ok value after → NativeMteTagCheck.TagStatusOK after) ∧
      (∀ i < n, t.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) := by
  have preparedShape := shape_of_prepared write acc prepared shape same
  obtain ⟨ad,t,run,fault,address,wb,vaEq,regs,mem,events,postNext,controlsNext,delta⟩ :=
    translation_from_closed spec config rows mapping m offset va n aligned pair write prepared s
      preparedShape catalogue controls (permitted prepared preparedShape) closed current mode post
      debug dcache pa mapped raw noUpd u frame
  refine ⟨ad,t,run,fault,address,wb,vaEq,regs,mem,events,postNext,controlsNext,delta,
    status_after_tme t (NativeMteTagCheck.tag_status_transport delta allowed),?_⟩
  intro i bound
  rw [mem]
  exact bytes i bound

#print axioms translation_from_closed
#print axioms have_tme_preserves
#print axioms status_after_tme
#print axioms shape_of_prepared
#print axioms translation_from_checked_bytes
end TranslateSpan.DefaultMTE2
