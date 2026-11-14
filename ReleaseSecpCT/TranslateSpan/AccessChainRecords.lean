-- secp CT0: records of ReadChain / WriteChain (Translate; page-walk side).
-- Each call appends its translation traffic (records = trafficRecsOf spec va: a function of (spec, va) only)
-- then one explicit access record (kind, VA, size). The records of a whole chain are the concatenation per call.
import TranslateSpan.DefaultAccessTrace
import HeapV2StepCerts.DataRecs
import ArmCertWalk.DataNoUpdate
import TranslateSpan.DefaultTranslation
import ArmCertWalk.NativeFetchPreserving
import ArmCertTranslateModel.CurrentProgramTransport
import HeapV2StepCerts.RawFetch
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace TranslateSpan.AccessChainRecords
open TranslateSpan.DefaultAccessTrace ArmCertWalk
open NativeAccess.Trace (Access)

abbrev Rec := ArmCertCTOrdered.OrderedEventV2.Record

/-- records of one data access: translation traffic at its VA, then the explicit access (kind, VA, size). -/
def accessRecs {domain : QueryDomain} (spec : TopologyImageSpec domain) (write : Bool) (r : Access) : List (Option Rec) :=
  (trafficRecsOf spec r.va).map (Option.map .traffic) ++
    [some (.access ⟨if write then .write else .read, BitVec.ofNat 64 r.va.toNat, r.bytes⟩)]

/-- Per-call hypothesis: the translation is a no-update walk over the declared slots, the descriptor's VA is the
request's, and the access kind is explicit (GPR data access). -/
def ReadCallOK {domain : QueryDomain} (spec : TopologyImageSpec domain) (c : ReadCall) : Prop :=
  NoUpdateTraffic spec c.request.va c.before.events c.packet.ad c.packet.translated.events ∧
  c.packet.ad.vaddress = c.request.va ∧ ∃ k, AccessDescriptor_to_Access_kind c.request.acc = .AK_explicit k

def WriteCallOK {domain : QueryDomain} (spec : TopologyImageSpec domain) (c : WriteCall) : Prop :=
  NoUpdateTraffic spec c.request.va c.before.events c.packet.ad c.packet.translated.events ∧
  c.packet.ad.vaddress = c.request.va ∧ ∃ k, AccessDescriptor_to_Access_kind c.request.acc = .AK_explicit k

theorem read_block_records {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (c : ReadCall) (ok : ReadCallOK spec c) :
    c.packet.block.toList.map ArmCertCTOrdered.OrderedEventV2.record = accessRecs spec false c.request := by
  obtain ⟨traffic, vaddr, k, hk⟩ := ok
  have h := HeapV2StepCerts.DataRecs.single_records (spec := spec) (va := c.request.va)
    (before := c.before.events) (after := c.packet.after.events) (delta := c.packet.block)
    ⟨c.packet.ad, c.packet.translated.events, traffic, c.packet.events⟩ c.packet.events_block nodup
  rw [h]
  simp only [accessRecs, ArmCertCTOrdered.OrderedEventV2.record, ArmCertCT.Native.V2.trafficRec, hk, vaddr,
    ArmCertCT.Native.projectEvent, Bool.false_eq_true, ↓reduceIte]

theorem write_block_records {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (c : WriteCall) (ok : WriteCallOK spec c) :
    c.packet.block.toList.map ArmCertCTOrdered.OrderedEventV2.record = accessRecs spec true c.request := by
  obtain ⟨traffic, vaddr, k, hk⟩ := ok
  have h := HeapV2StepCerts.DataRecs.single_records (spec := spec) (va := c.request.va)
    (before := c.before.events) (after := c.packet.after.events) (delta := c.packet.block)
    ⟨c.packet.ad, c.packet.translated.events, traffic, c.packet.events⟩ c.packet.events_block nodup
  rw [h]
  simp only [accessRecs, ArmCertCTOrdered.OrderedEventV2.record, ArmCertCT.Native.V2.trafficRec, hk, vaddr,
    ArmCertCT.Native.projectEvent, ↓reduceIte]

/-- **ReadChain → records** (any call list: one 16-byte call, two 8-byte calls, or bytewise). -/
theorem readChain_records {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) {a b : TranslateSpan.DefaultAccessTrace.State} {calls : List ReadCall}
    (h : ReadChain a calls b) (ok : ∀ c ∈ calls, ReadCallOK spec c) :
    ∃ d : Array Event, b.events = a.events ++ d ∧
      d.toList.map ArmCertCTOrdered.OrderedEventV2.record =
        (calls.map ReadCall.request).flatMap (accessRecs spec false) := by
  induction h with
  | nil f => exact ⟨#[], by rw [f.2.2.1]; simp, rfl⟩
  | cons c f tail ih =>
    obtain ⟨d, hd, hr⟩ := ih (fun c' m => ok c' (List.mem_cons_of_mem _ m))
    refine ⟨c.packet.block ++ d, ?_, ?_⟩
    · rw [hd, c.packet.events_block, f.2.2.1, Array.append_assoc]
    · rw [Array.toList_append, List.map_append, read_block_records spec nodup c (ok c List.mem_cons_self), hr]
      rfl

/-- **WriteChain → records**. -/
theorem writeChain_records {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) {a b : TranslateSpan.DefaultAccessTrace.State} {calls : List WriteCall}
    (h : WriteChain a calls b) (ok : ∀ c ∈ calls, WriteCallOK spec c) :
    ∃ d : Array Event, b.events = a.events ++ d ∧
      d.toList.map ArmCertCTOrdered.OrderedEventV2.record =
        (calls.map WriteCall.request).flatMap (accessRecs spec true) := by
  induction h with
  | nil f => exact ⟨#[], by rw [f.2.2.1]; simp, rfl⟩
  | cons c f tail ih =>
    obtain ⟨d, hd, hr⟩ := ih (fun c' m => ok c' (List.mem_cons_of_mem _ m))
    refine ⟨c.packet.block ++ d, ?_, ?_⟩
    · rw [hd, c.packet.events_block, f.2.2.1, Array.append_assoc]
    · rw [Array.toList_append, List.map_append, write_block_records spec nodup c (ok c List.mem_cons_self), hr]
      rfl

/-! ## Bridge: the per-call hypothesis from the packet's own translation + the current-walk premises -/

theorem readCallOK_of {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (c : ReadCall) (q : AccessQuery)
    (qva : q.va = c.request.va) (qraw : q.request.raw = c.packet.prepared)
    (qal : q.request.aligned = c.request.aligned) (qsz : q.size = (c.request.bytes : Int))
    (member : domain q) (data : S1AccessData spec config rows q)
    (current : CurrentS1At spec config rows c.before)
    (access : CurrentS1AccessAt spec config rows mapping q data c.before)
    (mode : HostEL0ModeAt c.before.regs) (aa64 : c.before.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt c.before.regs) (spe : c.before.regs.bank_Bool .SPESampleInFlight = false)
    (notFetch : (q.request.raw.acctype == .AccessType_IFETCH) = false)
    (dcache : currentDCache c.before.regs = true)
    (pa : BitVec 56) (mapped : mapping q.va = some pa.toNat)
    (raw : RawImageAt spec.imageRows c.before.mem)
    (none : NoUpdateRows {spec.params with haft := hostHAFT c.before.regs} q.request.raw spec.imageRows = true)
    (explicit : ∃ k, AccessDescriptor_to_Access_kind c.request.acc = .AK_explicit k) :
    ReadCallOK spec c := by
  obtain ⟨ad, t1, run, _, _, _, _, _, vaddr, _, _, traffic⟩ :=
    translate_noupdate_at spec config rows mapping q member data c.before c.packet.translationInput
      c.packet.choiceFrame.1 c.packet.choiceFrame.2.1 current access mode aa64 debug spe notFetch dcache pa mapped raw none
  have hrun : AArch64_TranslateAddress c.request.va c.packet.prepared c.request.aligned (c.request.bytes : Int)
      c.packet.translationInput = .ok ad t1 := by rw [← qva, ← qraw, ← qal, ← qsz]; exact run
  have e := hrun.symm.trans c.packet.translation
  obtain ⟨h1, h2⟩ := EStateM.Result.ok.inj e
  subst h1; subst h2
  refine ⟨?_, by rw [vaddr, qva], explicit⟩
  rw [← qva, ← c.packet.choiceFrame.2.2.1]; exact traffic

theorem writeCallOK_of {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (c : WriteCall) (q : AccessQuery)
    (qva : q.va = c.request.va) (qraw : q.request.raw = c.packet.prepared)
    (qal : q.request.aligned = c.request.aligned) (qsz : q.size = (c.request.bytes : Int))
    (member : domain q) (data : S1AccessData spec config rows q)
    (current : CurrentS1At spec config rows c.before)
    (access : CurrentS1AccessAt spec config rows mapping q data c.before)
    (mode : HostEL0ModeAt c.before.regs) (aa64 : c.before.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt c.before.regs) (spe : c.before.regs.bank_Bool .SPESampleInFlight = false)
    (notFetch : (q.request.raw.acctype == .AccessType_IFETCH) = false)
    (dcache : currentDCache c.before.regs = true)
    (pa : BitVec 56) (mapped : mapping q.va = some pa.toNat)
    (raw : RawImageAt spec.imageRows c.before.mem)
    (none : NoUpdateRows {spec.params with haft := hostHAFT c.before.regs} q.request.raw spec.imageRows = true)
    (explicit : ∃ k, AccessDescriptor_to_Access_kind c.request.acc = .AK_explicit k) :
    WriteCallOK spec c := by
  obtain ⟨ad, t1, run, _, _, _, _, _, vaddr, _, _, traffic⟩ :=
    translate_noupdate_at spec config rows mapping q member data c.before c.packet.translationInput
      c.packet.choiceFrame.1 c.packet.choiceFrame.2.1 current access mode aa64 debug spe notFetch dcache pa mapped raw none
  have hrun : AArch64_TranslateAddress c.request.va c.packet.prepared c.request.aligned (c.request.bytes : Int)
      c.packet.translationInput = .ok ad t1 := by rw [← qva, ← qraw, ← qal, ← qsz]; exact run
  have e := hrun.symm.trans c.packet.translation
  obtain ⟨h1, h2⟩ := EStateM.Result.ok.inj e
  subst h1; subst h2
  refine ⟨?_, by rw [vaddr, qva], explicit⟩
  rw [← qva, ← c.packet.choiceFrame.2.2.1]; exact traffic

/-! ## From the closed-membership/current facts at the call's own state (what every PairDefault236 path has) -/

theorem readCallOK_of_current {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (c : ReadCall)
    (closed : ClosedMembershipAt spec config rows mapping m c.before)
    (current : CurrentS1At spec config rows c.before)
    (mode : HostEL0ModeAt c.before.regs) (post : MemM1.MemReadD.PostRegs c.before.regs)
    (debug : ExistingE11DebugAt c.before.regs) (dcache : currentDCache c.before.regs = true)
    (raw : RawImageAt spec.imageRows c.before.mem)
    (noUpd : ∀ wr a, DataShape wr a → NoUpdateRows {spec.params with haft := hostHAFT c.before.regs} a spec.imageRows = true)
    (shape : DataShape false c.packet.prepared)
    (permitted : m.permitted c.request.va c.packet.prepared c.request.aligned (c.request.bytes : Int))
    (pa : BitVec 56) (mapped : mapping c.request.va = some pa.toNat)
    (explicit : ∃ k, AccessDescriptor_to_Access_kind c.request.acc = .AK_explicit k) :
    ReadCallOK spec c := by
  obtain ⟨⟨qva,⟨qacc,qal⟩,qn⟩,hva,hacc,hal,hn,member,data,access⟩ :=
    closed c.request.va c.packet.prepared c.request.aligned (c.request.bytes : Int) permitted
  simp only at hva hacc hal hn
  exact readCallOK_of spec config rows mapping c _ hva hacc hal hn member data current access mode post.aa64el0 debug
    post.spe (by show (qacc.acctype == .AccessType_IFETCH) = false; rw [hacc, shape.acctype]; rfl) dcache pa
    (by simpa only [hva] using mapped) raw (by simpa only [hacc] using noUpd _ _ shape) explicit

theorem writeCallOK_of_current {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (c : WriteCall)
    (closed : ClosedMembershipAt spec config rows mapping m c.before)
    (current : CurrentS1At spec config rows c.before)
    (mode : HostEL0ModeAt c.before.regs) (post : MemM1.MemReadD.PostRegs c.before.regs)
    (debug : ExistingE11DebugAt c.before.regs) (dcache : currentDCache c.before.regs = true)
    (raw : RawImageAt spec.imageRows c.before.mem)
    (noUpd : ∀ wr a, DataShape wr a → NoUpdateRows {spec.params with haft := hostHAFT c.before.regs} a spec.imageRows = true)
    (shape : DataShape true c.packet.prepared)
    (permitted : m.permitted c.request.va c.packet.prepared c.request.aligned (c.request.bytes : Int))
    (pa : BitVec 56) (mapped : mapping c.request.va = some pa.toNat)
    (explicit : ∃ k, AccessDescriptor_to_Access_kind c.request.acc = .AK_explicit k) :
    WriteCallOK spec c := by
  obtain ⟨⟨qva,⟨qacc,qal⟩,qn⟩,hva,hacc,hal,hn,member,data,access⟩ :=
    closed c.request.va c.packet.prepared c.request.aligned (c.request.bytes : Int) permitted
  simp only at hva hacc hal hn
  exact writeCallOK_of spec config rows mapping c _ hva hacc hal hn member data current access mode post.aa64el0 debug
    post.spe (by show (qacc.acctype == .AccessType_IFETCH) = false; rw [hacc, shape.acctype]; rfl) dcache pa
    (by simpa only [hva] using mapped) raw (by simpa only [hacc] using noUpd _ _ shape) explicit

/-! ## Whole-chain discharge from the facts at the chain's start state (no E copies of the run lemmas needed) -/

/-- Every call of a ReadChain starts at the chain-start registers and memory (reads change neither). -/
theorem readChain_before {a b : TranslateSpan.DefaultAccessTrace.State} {calls : List ReadCall} (h : ReadChain a calls b) :
    ∀ c ∈ calls, c.before.regs = a.regs ∧ c.before.mem = a.mem := by
  induction h with
  | nil f => intro c hc; cases hc
  | cons c f tail ih =>
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | m
    · exact ⟨f.1, f.2.1⟩
    · obtain ⟨r, mm⟩ := ih c' m
      exact ⟨r.trans (c.packet.registers.trans f.1), mm.trans (c.packet.memory.trans f.2.1)⟩

/-- Every call of a WriteChain starts at the chain-start registers (writes change memory, not registers). -/
theorem writeChain_before {a b : TranslateSpan.DefaultAccessTrace.State} {calls : List WriteCall} (h : WriteChain a calls b) :
    ∀ c ∈ calls, c.before.regs = a.regs := by
  induction h with
  | nil f => intro c hc; cases hc
  | cons c f tail ih =>
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | m
    · exact f.1
    · exact (ih c' m).trans (c.packet.registers.trans f.1)

/-- **All calls of a ReadChain are ReadCallOK**, from the closed/current facts at the chain start plus, per call,
the request's data shape, its consumer permission (for any prepared descriptor), its mapping, and explicit kind. -/
theorem readChain_ok {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    {a b : TranslateSpan.DefaultAccessTrace.State} {calls : List ReadCall} (h : ReadChain a calls b)
    (closed : ClosedMembershipAt spec config rows mapping m a) (current : CurrentS1At spec config rows a)
    (mode : HostEL0ModeAt a.regs) (post : MemM1.MemReadD.PostRegs a.regs)
    (debug : ExistingE11DebugAt a.regs) (dcache : currentDCache a.regs = true)
    (raw : RawImageAt spec.imageRows a.mem)
    (noUpd : ∀ wr x, DataShape wr x → NoUpdateRows {spec.params with haft := hostHAFT a.regs} x spec.imageRows = true)
    (per : ∀ c ∈ calls, DataShape false c.request.acc ∧
      (∀ prepared, DataShape false prepared → m.permitted c.request.va prepared c.request.aligned (c.request.bytes : Int)) ∧
      (∃ pa : BitVec 56, mapping c.request.va = some pa.toNat) ∧
      ∃ k, AccessDescriptor_to_Access_kind c.request.acc = .AK_explicit k) :
    ∀ c ∈ calls, ReadCallOK spec c := by
  intro c hc
  obtain ⟨r, mm⟩ := readChain_before h c hc
  obtain ⟨shape, perm, ⟨pa, mapped⟩, explicit⟩ := per c hc
  have pshape := TranslateSpan.DefaultMTE2.shape_of_prepared false c.request.acc c.packet.prepared shape c.packet.preparedShape
  obtain ⟨⟨qva,⟨qacc,qal⟩,qn⟩,hva,hacc,hal,hn,member,data,access⟩ :=
    closed c.request.va c.packet.prepared c.request.aligned (c.request.bytes : Int) (perm _ pshape)
  simp only at hva hacc hal hn
  exact readCallOK_of spec config rows mapping c _ hva hacc hal hn member data (current_s1_frame current r mm)
    (access.of_regs r) (by rw [r]; exact mode) (by rw [r]; exact post.aa64el0) (by rw [r]; exact debug)
    (by rw [r]; exact post.spe) (by show (qacc.acctype == .AccessType_IFETCH) = false; rw [hacc, pshape.acctype]; rfl)
    (by rw [r]; exact dcache) pa (by simpa only [hva] using mapped) (by rw [mm]; exact raw)
    (by rw [r]; simpa only [hacc] using noUpd _ _ pshape) explicit

/-- **All calls of a WriteChain are WriteCallOK**. Register facts come from the chain start; the memory-dependent
ones (current walk, raw image) are per call, since earlier writes change memory. -/
theorem writeChain_ok {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    {a b : TranslateSpan.DefaultAccessTrace.State} {calls : List WriteCall} (h : WriteChain a calls b)
    (closed : ClosedMembershipAt spec config rows mapping m a)
    (mode : HostEL0ModeAt a.regs) (post : MemM1.MemReadD.PostRegs a.regs)
    (debug : ExistingE11DebugAt a.regs) (dcache : currentDCache a.regs = true)
    (noUpd : ∀ wr x, DataShape wr x → NoUpdateRows {spec.params with haft := hostHAFT a.regs} x spec.imageRows = true)
    (per : ∀ c ∈ calls, DataShape true c.request.acc ∧
      (∀ prepared, DataShape true prepared → m.permitted c.request.va prepared c.request.aligned (c.request.bytes : Int)) ∧
      (∃ pa : BitVec 56, mapping c.request.va = some pa.toNat) ∧
      (∃ k, AccessDescriptor_to_Access_kind c.request.acc = .AK_explicit k) ∧
      CurrentS1At spec config rows c.before ∧ RawImageAt spec.imageRows c.before.mem) :
    ∀ c ∈ calls, WriteCallOK spec c := by
  intro c hc
  have r := writeChain_before h c hc
  obtain ⟨shape, perm, ⟨pa, mapped⟩, explicit, current, raw⟩ := per c hc
  have pshape := TranslateSpan.DefaultMTE2.shape_of_prepared true c.request.acc c.packet.prepared shape c.packet.preparedShape
  obtain ⟨⟨qva,⟨qacc,qal⟩,qn⟩,hva,hacc,hal,hn,member,data,access⟩ :=
    closed c.request.va c.packet.prepared c.request.aligned (c.request.bytes : Int) (perm _ pshape)
  simp only at hva hacc hal hn
  exact writeCallOK_of spec config rows mapping c _ hva hacc hal hn member data current
    (access.of_regs r) (by rw [r]; exact mode) (by rw [r]; exact post.aa64el0) (by rw [r]; exact debug)
    (by rw [r]; exact post.spe) (by show (qacc.acctype == .AccessType_IFETCH) = false; rw [hacc, pshape.acctype]; rfl)
    (by rw [r]; exact dcache) pa (by simpa only [hva] using mapped) raw
    (by rw [r]; simpa only [hacc] using noUpd _ _ pshape) explicit

/-! ## Stores: transport the current walk / raw image across the chain's own writes (table-separated) -/

/-- The physical bytes written by a list of write calls. -/
def written (calls : List WriteCall) : Nat → Prop := fun x =>
  ∃ c ∈ calls, c.packet.ad.paddress.address.toNat ≤ x ∧ x < c.packet.ad.paddress.address.toNat + c.request.bytes

/-- Every call of a WriteChain sees the chain-start memory except at bytes written by the chain's calls. -/
theorem writeChain_mem {a b : TranslateSpan.DefaultAccessTrace.State} {calls : List WriteCall} (h : WriteChain a calls b) :
    ∀ c ∈ calls, WritesOnly (written calls) (fun x => a.mem[x]?) (fun x => c.before.mem[x]?) := by
  induction h with
  | nil f => intro c hc; cases hc
  | cons c f tail ih =>
    intro c' hc' x hx
    rcases List.mem_cons.mp hc' with rfl | m
    · simp only [f.2.1]
    · have notTail : ¬ written _ x := fun ⟨d, hd, lo, hi⟩ => hx ⟨d, List.mem_cons_of_mem _ hd, lo, hi⟩
      have notC : ¬ (c.packet.ad.paddress.address.toNat ≤ x ∧ x < c.packet.ad.paddress.address.toNat + c.request.bytes) :=
        fun w => hx ⟨c, List.mem_cons_self, w⟩
      have e := ih c' m x notTail
      simp only at e ⊢
      rw [e, c.packet.memory, MemM1.MemWriteD1.wfold_get, if_neg notC, f.2.1]

/-- **writeChain_ok, store-separated form**: from the chain-start facts (incl. CurrentS1At / RawImageAt at the start)
and 'no written byte is a table byte', every call is WriteCallOK. -/
theorem writeChain_ok_sep {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    {a b : TranslateSpan.DefaultAccessTrace.State} {calls : List WriteCall} (h : WriteChain a calls b)
    (closed : ClosedMembershipAt spec config rows mapping m a) (current : CurrentS1At spec config rows a)
    (mode : HostEL0ModeAt a.regs) (post : MemM1.MemReadD.PostRegs a.regs)
    (debug : ExistingE11DebugAt a.regs) (dcache : currentDCache a.regs = true)
    (raw : RawImageAt spec.imageRows a.mem)
    (noUpd : ∀ wr x, DataShape wr x → NoUpdateRows {spec.params with haft := hostHAFT a.regs} x spec.imageRows = true)
    (outside : ∀ c ∈ calls, ∀ i < c.request.bytes,
      ¬ (rowsFootprint spec.imageRows).byte (c.packet.ad.paddress.address.toNat + i))
    (per : ∀ c ∈ calls, DataShape true c.request.acc ∧
      (∀ prepared, DataShape true prepared → m.permitted c.request.va prepared c.request.aligned (c.request.bytes : Int)) ∧
      (∃ pa : BitVec 56, mapping c.request.va = some pa.toNat) ∧
      ∃ k, AccessDescriptor_to_Access_kind c.request.acc = .AK_explicit k) :
    ∀ c ∈ calls, WriteCallOK spec c := by
  have sep : Separated (rowsFootprint spec.imageRows).byte (written calls) := by
    intro x tbl ⟨d, hd, lo, hi⟩
    have := outside d hd (x - d.packet.ad.paddress.address.toNat) (by omega)
    rw [show d.packet.ad.paddress.address.toNat + (x - d.packet.ad.paddress.address.toNat) = x by omega] at this
    exact this tbl
  apply writeChain_ok spec config rows mapping m h closed mode post debug dcache noUpd
  intro c hc
  obtain ⟨shape, perm, mapped, explicit⟩ := per c hc
  have r := writeChain_before h c hc
  have wo := writeChain_mem h c hc
  refine ⟨shape, perm, mapped, explicit, ?_, HeapV2StepCerts.RawFetch.raw_writes raw wo sep⟩
  exact current_s1_program_write current (written calls) wo sep (by rw [r]) (by rw [r]) (by rw [r]) (by rw [r])
    (by rw [r]) (by rw [r]) (by rw [r]) (by rw [r]) (by rw [r]) (by rw [r]) (fun _ => by rw [r]) (fun _ => by rw [r])
    (fun _ => by rw [r]) (by rw [r])

end TranslateSpan.AccessChainRecords

#print axioms TranslateSpan.AccessChainRecords.readChain_records
#print axioms TranslateSpan.AccessChainRecords.writeChain_records
#print axioms TranslateSpan.AccessChainRecords.readCallOK_of
#print axioms TranslateSpan.AccessChainRecords.writeCallOK_of
#print axioms TranslateSpan.AccessChainRecords.readCallOK_of_current
#print axioms TranslateSpan.AccessChainRecords.writeCallOK_of_current
#print axioms TranslateSpan.AccessChainRecords.readChain_ok
#print axioms TranslateSpan.AccessChainRecords.writeChain_ok
#print axioms TranslateSpan.AccessChainRecords.writeChain_mem
#print axioms TranslateSpan.AccessChainRecords.writeChain_ok_sep
