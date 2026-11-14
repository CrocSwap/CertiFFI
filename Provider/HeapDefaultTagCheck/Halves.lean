import HeapDefaultTagCheck.Access
import ArmCertWalk.MemPair
import DefaultPairNoUpdate
import DefaultReadTrace8
import DefaultStoreTrace
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open S1Normality MemM1.MemReadD MemM1.MemReadD2 MemM1.MemWriteD1 MemM1.MemWriteD4 MemM1.MemWriteD5
open NativeMteTagCheck NativeMteTagCheck.StatusTrace ReleaseProfile ReleaseProfile.DefaultStoreNoUpdate MemM1.MemReadIF
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace HeapDefaultTagCheck.Halves
abbrev State := NativeMteTagCheck.State
theorem half_read {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s u : State) (fr : NativeMteTagCheck.StatusTrace.TraceFrame s u) (va : BitVec 64) (aligned : va.toNat % 8 = 0) (acc : AccessDescriptor)
    (hA : AccDR2 acc) (shape : DataShape false acc)
    (perAcc : ∀ prepared, DataShape false prepared →
      domain ⟨va,⟨prepared,true⟩,(8 : Int)⟩ ∧
      ∃ data : S1AccessData spec config rows ⟨va,⟨prepared,true⟩,(8 : Int)⟩,
        CurrentS1AccessAt spec config rows mapping ⟨va,⟨prepared,true⟩,(8 : Int)⟩ data s)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs s.regs) (catalogue : ControlCatalogue) (controls : DefaultAt catalogue s)
    (allowed : TagStatusOK s) (el : acc.el = EL0)
    (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping va = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : ∀ prepared, DataShape false prepared →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} prepared spec.imageRows = true)
    (value : BitVec (8 * 8)) (bytes : ∀ i < 8, s.mem[pa.toNat + i]? = some (value.extractLsb' (8 * i) 8)) :
    ∃ ad mid t draws, AArch64_MemSingle_read__1 va 8 acc true false u = .ok value t ∧
      NoUpdateTraffic spec va s.events ad mid ∧ ad.vaddress = va ∧
      t.events = mid.push (.memRead pa.toNat 8 (some va.toNat) (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ ChoiceDelta s t draws ∧ draws ≤ 1 := by
  obtain ⟨ad,t1,t,draws,⟨regs1,mem1,vaddr,traffic⟩,_,run,events,regs,mem,delta,bound⟩ :=
    DefaultRead8.single8_trace va true false aligned acc u pa value hA catalogue (controls.transport (NativeMteTagCheck.StatusTrace.to_frame fr)) el
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
            va 8 prepared preparedA catalogue controls allowed member data current access
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

theorem half_set {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s u : State) (fr : TraceFrame s u) (va : BitVec 64) (n : Nat) (hn : SizeOK n)
    (aligned : va.toNat % n = 0) (acc : AccessDescriptor) (hA : AccDWT acc)
    (shape : DataShape true acc) (el : acc.el = EL0)
    (catalogue : ControlCatalogue) (controls : DefaultAt catalogue s) (allowed : TagStatusOK s)
    (v : BitVec (n * 8))
    (perAcc : ∀ prepared, DataShape true prepared →
      domain (storeQuery va n prepared) ∧ ∃ data : S1AccessData spec config rows (storeQuery va n prepared),
        CurrentS1AccessAt spec config rows mapping (storeQuery va n prepared) data s)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (pr : PostRegs s.regs) (debug : ExistingE11DebugAt s.regs)
    (dcache : currentDCache s.regs = true) (pa : BitVec 56) (mapped : mapping va = some pa.toNat)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : ∀ prepared, DataShape true prepared →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} prepared spec.imageRows = true)
    (mmio : NotMMIO pa) :
    ∃ ad middle fin draws, AArch64_MemSingle_set__1 va n acc true false v u = .ok () fin ∧
      NoUpdateTraffic spec va s.events ad middle ∧ ad.vaddress = va ∧
      fin.events = middle.push (.memWrite pa.toNat n (some va.toNat)
        (AccessDescriptor_to_Access_kind acc) (some (Sail.BitVec.castWidth (m := 8 * n) v)) Option.none) ∧
      fin.regs = s.regs ∧ fin.mem = wfold s.mem pa.toNat n
        (fun j => (Sail.BitVec.castWidth (m := 8 * n) v).extractLsb' (8 * j) 8) ∧
      ChoiceDelta s fin draws ∧ draws ≤ 1 := by
  obtain ⟨ad, t1, fin, draws, ⟨r, m, hv, traffic⟩, call, events, regs, mem, delta, bound⟩ :=
    DefaultStores.store_natural_trace va n hn true false aligned acc u pa v hA
      catalogue (controls.transport (to_frame fr)) el
      (fun ad t1 => t1.regs = s.regs ∧ t1.mem = s.mem ∧ ad.vaddress = va ∧
        NoUpdateTraffic spec va s.events ad t1.events)
      (by
        intro prepared w same fw
        have preparedShape : DataShape true prepared := by
          rw [same]
          exact ⟨shape.acctype,shape.el,shape.ss,shape.read,shape.write,shape.tagaccess,
            shape.transactional,shape.nonfault,shape.contiguous,shape.firstfault,shape.first,shape.ls64⟩
        have preparedA : AccDWT prepared := by
          rw [same]
          exact ⟨⟨hA.base.ss,hA.base.el,hA.base.gpr,hA.base.tag,hA.base.ls64,hA.base.tx,
            hA.base.nf,hA.base.ff⟩,hA.exclusive,hA.atomicop,hA.acqsc,hA.acqpc,hA.relsc⟩
        obtain ⟨member,data,access⟩ := perAcc prepared preparedShape
        exact translate spec config rows mapping s w (NativeMteTagCheck.StatusTrace.frame_trans fr fw)
          va n prepared preparedA catalogue controls allowed member data current access mode pr debug
          dcache pa mapped raw (none prepared preparedShape))
      mmio
  refine ⟨ad, t1.events, fin, draws, call, traffic, hv, by rw [events, hv],
    regs.trans r, by rw [mem, m], ?_, bound⟩
  simpa only [Nat.zero_add] using choice_delta_trans fr.2.2.2 delta

theorem default_of_regs {catalogue : ControlCatalogue} {s t : State}
    (h : DefaultAt catalogue s) (regs : t.regs = s.regs) : DefaultAt catalogue t := by
  rcases h with ⟨⟨el,nrw,aa,rme,vhe,ns,e2h,tge⟩,mte,tco,tcf,prep⟩
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  all_goals (try unfold PreparationAt) <;> rw [regs] <;> assumption

#print axioms half_read
#print axioms half_set
end HeapDefaultTagCheck.Halves
