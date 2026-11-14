import DefaultNaturalReadTrace
import DefaultSPChoice
import DefaultStoreNoUpdate

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open S1Normality MemM1.MemReadD MemM1.MemReadD2 MemM1.MemWriteD5
open NativeMteTagCheck ReleaseProfile
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000

namespace HeapDefaultTagCheck.Access
abbrev State := NativeMteTagCheck.State


theorem load1 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s u : State) (fr : NativeMteTagCheck.StatusTrace.TraceFrame s u) (va : BitVec 64) (acc : AccessDescriptor)
    (hA : AccDR2 acc) (shape : DataShape false acc)
    (perAcc : ∀ prepared, DataShape false prepared →
      domain ⟨va,⟨prepared,true⟩,(1 : Int)⟩ ∧
      ∃ data : S1AccessData spec config rows ⟨va,⟨prepared,true⟩,(1 : Int)⟩,
        CurrentS1AccessAt spec config rows mapping ⟨va,⟨prepared,true⟩,(1 : Int)⟩ data s)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs s.regs) (catalogue : ControlCatalogue) (controls : DefaultAt catalogue s)
    (allowed : TagStatusOK s) (el : acc.el = EL0)
    (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping va = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : ∀ prepared, DataShape false prepared →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} prepared spec.imageRows = true)
    (value : BitVec (1 * 8)) (bytes : ∀ i < 1, s.mem[pa.toNat + i]? = some (value.extractLsb' (8 * i) 8)) :
    ∃ ad mid t draws, Mem_read va 1 acc u = .ok value t ∧
      NoUpdateTraffic spec va s.events ad mid ∧ ad.vaddress = va ∧
      t.events = mid.push (.memRead pa.toNat 1 (some va.toNat) (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ ChoiceDelta s t draws ∧ draws ≤ 1 := by
  obtain ⟨ad,t1,t,draws,⟨regs1,mem1,vaddr,traffic⟩,run,events,regs,mem,delta,bound⟩ :=
    DefaultNaturalReads.memRead1_trace va acc u pa value hA catalogue (controls.transport (NativeMteTagCheck.StatusTrace.to_frame fr)) el
      (fun ad t1 => t1.regs = s.regs ∧ t1.mem = s.mem ∧ ad.vaddress = va ∧
        NoUpdateTraffic spec va s.events ad t1.events)
      (by
        intro prepared u same frame
        have preparedShape : DataShape false prepared := by
          rw [same]
          exact ⟨shape.acctype,shape.el,shape.ss,shape.read,shape.write,shape.tagaccess,
            shape.transactional,shape.nonfault,shape.contiguous,shape.firstfault,shape.first,shape.ls64⟩
        have preparedA : AccDWT prepared := by
          rw [same]
          exact ⟨⟨shape.ss,shape.el,shape.acctype,shape.tagaccess,shape.ls64,shape.transactional,
            shape.nonfault,shape.firstfault⟩,hA.exclusive,hA.atomicop,hA.acqsc,hA.acqpc,hA.relsc⟩
        obtain ⟨member,data,access⟩ := perAcc prepared preparedShape
        obtain ⟨ad,t1,call,fault,address,normal,inner,outer,_,controlsNext,statusNext,
          r,m,hva,walks⟩ := DefaultStoreNoUpdate.translate spec config rows mapping s _ (NativeMteTagCheck.StatusTrace.frame_trans fr frame)
            va 1 prepared preparedA catalogue controls allowed member data current access
            mode post debug dcache pa mapped raw (noUpd prepared preparedShape)
        refine ⟨ad,t1,call,fault,address,normal,inner,outer,by rw [r]; exact post,
          controlsNext,statusNext,?_,r,m,hva,walks⟩
        intro i bound
        rw [m]
        exact bytes i bound)
      mmio
  refine ⟨ad,t1.events,t,draws,run,traffic,vaddr,by rw [events,vaddr],
    regs.trans regs1,mem.trans mem1,?_,bound⟩
  simpa only [Nat.zero_add] using choice_delta_trans fr.2.2.2 delta

#print axioms load1
end HeapDefaultTagCheck.Access

namespace HeapDefaultTagCheck.Access
open NativeMteTagCheck
 theorem status_at {entry current : State} {capacity used : Nat}
    (rows : TagStatusRows entry (entry.choiceOcc.getD 1354 0) capacity)
    (delta : ChoiceDelta entry current used) (within : used < capacity) : TagStatusOK current :=
  tag_status_of_rows entry current (entry.choiceOcc.getD 1354 0) capacity used rows delta.1 delta.2 within
 theorem prepared_shape {wr : Bool} {acc prepared : AccessDescriptor}
    (shape : DataShape wr acc) (same : prepared = {acc with tagchecked := prepared.tagchecked}) :
    DataShape wr prepared := by
  rw [same]
  exact ⟨shape.acctype,shape.el,shape.ss,shape.read,shape.write,shape.tagaccess,
    shape.transactional,shape.nonfault,shape.contiguous,shape.firstfault,shape.first,shape.ls64⟩
end HeapDefaultTagCheck.Access
