import DefaultNaturalStoreTrace
import ArmCertWalk.DataNoUpdate

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open NativeMte2 S1Normality MemM1.MemReadIF MemM1.MemReadD
open MemM1.MemWriteD1 MemM1.MemWriteD5
open NativeMteTagCheck NativeMteTagCheck.StatusTrace
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.DefaultStoreNoUpdate
abbrev State := NativeMteTagCheck.State

def storeQuery (va : BitVec 64) (n : Nat) (acc : AccessDescriptor) : AccessQuery :=
  ⟨va, ⟨acc, true⟩, (n : Int)⟩

#check "CURRENT_DECL default store translate"
theorem translate {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s u : State) (fr : TraceFrame s u)
    (va : BitVec 64) (n : Nat) (acc : AccessDescriptor) (hA : AccDWT acc)
    (catalogue : ControlCatalogue) (controls : DefaultAt catalogue s) (allowed : TagStatusOK s)
    (member : domain (storeQuery va n acc)) (data : S1AccessData spec config rows (storeQuery va n acc))
    (current : CurrentS1At spec config rows s)
    (access : CurrentS1AccessAt spec config rows mapping (storeQuery va n acc) data s)
    (mode : HostEL0ModeAt s.regs) (pr : PostRegs s.regs) (debug : ExistingE11DebugAt s.regs)
    (dcache : currentDCache s.regs = true) (pa : BitVec 56) (mapped : mapping va = some pa.toNat)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true) :
    ∃ ad t1, AArch64_TranslateAddress va acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ t1.regs.bank_Bool .SPESampleInFlight = false ∧
      DefaultAt catalogue t1 ∧
      (∀ value after, HaveTME () t1 = .ok value after → TagStatusOK after) ∧
      t1.regs = s.regs ∧ t1.mem = s.mem ∧ ad.vaddress = va ∧
      NoUpdateTraffic spec va s.events ad t1.events := by
  have notFetch : ((storeQuery va n acc).request.raw.acctype == .AccessType_IFETCH) = false := by
    change (acc.acctype == .AccessType_IFETCH) = false
    rw [hA.base.gpr]; rfl
  obtain ⟨ad, t1, run, fault, paddr, normal, inner, outer, vaddr, regs, mem, traffic⟩ :=
    translate_noupdate_at spec config rows mapping (storeQuery va n acc) member data
      s u fr.1 fr.2.1 current access mode pr.aa64el0 debug pr.spe notFetch dcache pa mapped raw none
  have delta : ChoiceDelta s t1 0 := by
    simpa only [Nat.add_zero] using choice_delta_trans fr.2.2.2
      (TagCheckFrames.translation_preserves va acc true (n : Int) u ad t1 run)
  have status := tag_status_transport delta allowed
  have controlsNext : DefaultAt catalogue t1 := by
    rcases controls with ⟨⟨el,nrw,aa64,rme,vhe,ns,e2h,tge⟩,mte2,tco,tcf0,preparation⟩
    refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
    all_goals (try unfold PreparationAt) <;> rw [regs] <;> assumption
  refine ⟨ad, t1, run, fault, by rw [paddr], normal, inner, outer,
    by rw [regs]; exact pr.spe, controlsNext, ?_, regs, mem, vaddr, ?_⟩
  · intro value after h
    cases h
    exact status
  · rw [← fr.2.2.1]; exact traffic

#check "CURRENT_DECL default store natural"
theorem natural {domain : QueryDomain} (spec : TopologyImageSpec domain)
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
    ∃ ad middle fin draws, Mem_set va n acc v u = .ok () fin ∧
      NoUpdateTraffic spec va s.events ad middle ∧ ad.vaddress = va ∧
      fin.events = middle.push (.memWrite pa.toNat n (some va.toNat)
        (AccessDescriptor_to_Access_kind acc) (some (Sail.BitVec.castWidth (m := 8 * n) v)) Option.none) ∧
      fin.regs = s.regs ∧ fin.mem = wfold s.mem pa.toNat n
        (fun j => (Sail.BitVec.castWidth (m := 8 * n) v).extractLsb' (8 * j) 8) ∧
      ChoiceDelta s fin draws ∧ draws ≤ 1 := by
  obtain ⟨ad, t1, fin, draws, ⟨r, m, hv, traffic⟩, call, events, regs, mem, delta, bound⟩ :=
    DefaultNaturalStores.memSet_trace va n hn aligned acc u pa v hA
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
      mmio (DefaultNaturalStores.littleEndian acc u hA (by rw [fr.1]; exact pr))
  refine ⟨ad, t1.events, fin, draws, call, traffic, hv, by rw [events, hv],
    regs.trans r, by rw [mem, m], ?_, bound⟩
  simpa only [Nat.zero_add] using choice_delta_trans fr.2.2.2 delta

#check "CURRENT_DECL default store pair"
theorem pair {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s u : State) (fr : TraceFrame s u) (va : BitVec 64)
    (aligned : va.toNat % 16 = 0) (acc : AccessDescriptor) (hA : AccDWT acc)
    (shape : DataShape true acc) (el : acc.el = EL0)
    (catalogue : ControlCatalogue) (controls : DefaultAt catalogue s) (allowed : TagStatusOK s)
    (v : BitVec (16 * 8)) (lse2 : u.regs.FeatureImpl[111] = true)
    (perAcc : ∀ prepared, DataShape true prepared →
      domain (storeQuery va 16 prepared) ∧ ∃ data : S1AccessData spec config rows (storeQuery va 16 prepared),
        CurrentS1AccessAt spec config rows mapping (storeQuery va 16 prepared) data s)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (pr : PostRegs s.regs) (debug : ExistingE11DebugAt s.regs)
    (dcache : currentDCache s.regs = true) (pa : BitVec 56) (mapped : mapping va = some pa.toNat)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : ∀ prepared, DataShape true prepared →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} prepared spec.imageRows = true)
    (mmio : NotMMIO pa) :
    ∃ ad middle fin draws, Mem_set__1 va 16 acc true v u = .ok () fin ∧
      NoUpdateTraffic spec va s.events ad middle ∧ ad.vaddress = va ∧
      fin.events = middle.push (.memWrite pa.toNat 16 (some va.toNat)
        (AccessDescriptor_to_Access_kind acc) (some (Sail.BitVec.castWidth (m := 8 * 16) v)) Option.none) ∧
      fin.regs = s.regs ∧ fin.mem = wfold s.mem pa.toNat 16
        (fun j => (Sail.BitVec.castWidth (m := 8 * 16) v).extractLsb' (8 * j) 8) ∧
      ChoiceDelta s fin draws ∧ draws ≤ 1 := by
  obtain ⟨ad, t1, fin, draws, ⟨r, m, hv, traffic⟩, call, events, regs, mem, delta, bound⟩ :=
    DefaultNaturalStores.memSetPair_trace va aligned acc u pa v hA
      catalogue (controls.transport (to_frame fr)) el lse2
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
          va 16 prepared preparedA catalogue controls allowed member data current access mode pr debug
          dcache pa mapped raw (none prepared preparedShape))
      mmio (DefaultNaturalStores.littleEndian acc u hA (by rw [fr.1]; exact pr))
  refine ⟨ad, t1.events, fin, draws, call, traffic, hv, by rw [events, hv],
    regs.trans r, by rw [mem, m], ?_, bound⟩
  simpa only [Nat.zero_add] using choice_delta_trans fr.2.2.2 delta

#print axioms translate
#print axioms natural
#print axioms pair
end ReleaseProfile.DefaultStoreNoUpdate
