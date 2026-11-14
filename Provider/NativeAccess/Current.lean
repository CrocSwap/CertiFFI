import NativeAccess.Payload
import ArmCertWalk.DataNoUpdate
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace NativeAccess.Current
open NativeAccess.Trace
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3 MemM1.MemWriteD5

theorem fold_events_append (xs : List (Nat × Bool × Array Event)) (base suffix : Array Event) :
    xs.foldl (fun es x => es ++ x.2.2) (base ++ suffix) =
      base ++ xs.foldl (fun es x => es ++ x.2.2) suffix := by
  induction xs generalizing suffix with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons,Array.append_assoc]
    exact ih _

/-- Exact translation traffic is a past event suffix, without identifying
states or assuming anything about later calls. -/
theorem traffic_prefix {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {va : BitVec 64} {before after : Array Event} {ad : AddressDescriptor}
    (traffic : NoUpdateTraffic spec va before ad after) :
    ∃ W, after = before ++ W := by
  rcases traffic with ⟨info,walk,leaf,middle,traffic,flags,leafFlag,slots,endEv⟩
  rcases traffic with ⟨mid,walkTraffic,leafTraffic,midEq⟩
  refine ⟨(walk.foldl (fun (es : Array Event) (x : Nat × Bool × Array Event) => es ++ x.2.2) #[Event.translationStart info] ++ leaf.2.2).push
    (.translationEnd ad), ?_⟩
  rw [endEv,midEq,walkTraffic.1]
  simp only [Array.push_eq_append]
  rw [fold_events_append]
  simp only [Array.append_assoc]

/-- The existing canonical current invariant discharges the actual per-call
translation constructor. Every request field comes from the one actual Access
record. There is no future translation/admission callback hypothesis. -/
theorem translation_facts {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (r : Access) (s : State)
    (member : domain ⟨r.va,⟨r.acc,r.aligned⟩,(r.bytes : Int)⟩)
    (data : S1AccessData spec config rows ⟨r.va,⟨r.acc,r.aligned⟩,(r.bytes : Int)⟩)
    (current : CurrentS1At spec config rows s)
    (access : CurrentS1AccessAt spec config rows mapping
      ⟨r.va,⟨r.acc,r.aligned⟩,(r.bytes : Int)⟩ data s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (notFetch : (r.acc.acctype == .AccessType_IFETCH) = false)
    (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping r.va = some pa.toNat)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : NoUpdateRows {spec.params with haft := hostHAFT s.regs} r.acc spec.imageRows = true)
    (u : State) (fu : Frame s u) :
    ∃ ad t1, AArch64_TranslateAddress r.va r.acc r.aligned (r.bytes : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      NormalWB ad ∧ ad.vaddress = r.va ∧ t1.regs = s.regs ∧ t1.mem = s.mem ∧
      ∃ W, t1.events = u.events ++ W := by
  rcases translate_noupdate_at spec config rows mapping
      ⟨r.va,⟨r.acc,r.aligned⟩,(r.bytes : Int)⟩ member data s u fu.1 fu.2.1
      current access mode aa64 debug spe notFetch dcache pa mapped raw none with
    ⟨ad,t1,run,nf,paddr,normal,inner,outer,va,regs,mem,traffic⟩
  rcases traffic_prefix traffic with ⟨W,ev⟩
  exact ⟨ad,t1,run,nf,by rw [paddr],⟨normal,inner,outer⟩,va,regs,mem,W,ev⟩

/-- A byte packet and its actual value, built from static current-query data,
current RAM and control facts. It has no future model-run premise. -/
theorem read_byte {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor) (aligned ispair : Bool) (s : State)
    (member : domain ⟨a,⟨acc,aligned⟩,((1 : Nat) : Int)⟩)
    (data : S1AccessData spec config rows ⟨a,⟨acc,aligned⟩,((1 : Nat) : Int)⟩)
    (current : CurrentS1At spec config rows s)
    (access : CurrentS1AccessAt spec config rows mapping
      ⟨a,⟨acc,aligned⟩,((1 : Nat) : Int)⟩ data s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs2 s.regs) (hA : AccDR2 acc) (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping a = some pa.toNat) (ram : NotMMIO pa)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (value : BitVec 8) (bytes : ∀ i < 1, s.mem[pa.toNat + i]? = some (value.extractLsb' (8 * i) 8)) :
    ∃ packet : ReadPacket ⟨offset,a,1,acc,aligned,ispair⟩ s, packet.data = value := by
  apply Payload.read_byte_packet_value offset a acc aligned ispair s pa value hA post.noMTE2 ram
  intro u fu
  have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hA.gpr]; rfl
  rcases translation_facts spec config rows mapping ⟨offset,a,1,acc,aligned,ispair⟩ s
      member data current access mode post.post.aa64el0 debug post.post.spe notFetch dcache
      pa mapped raw none u fu with ⟨ad,t1,run,nf,paddr,wb,va,regs,mem,W,events⟩
  refine ⟨ad,t1,run,nf,paddr,wb.normal,wb.inner,wb.outer,?_,?_,W,?_,?_,events⟩
  · rw [regs]; exact post
  · intro i hi
    rw [mem]; exact bytes i hi
  · exact regs.trans fu.1.symm
  · exact mem.trans fu.2.1.symm

theorem read8_natural {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor) (aligned ispair : Bool) (natural : a.toNat % 8 = 0) (s : State)
    (member : domain ⟨a,⟨acc,aligned⟩,((8 : Nat) : Int)⟩)
    (data : S1AccessData spec config rows ⟨a,⟨acc,aligned⟩,((8 : Nat) : Int)⟩)
    (current : CurrentS1At spec config rows s)
    (access : CurrentS1AccessAt spec config rows mapping
      ⟨a,⟨acc,aligned⟩,((8 : Nat) : Int)⟩ data s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs2 s.regs) (hA : AccDR2 acc) (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping a = some pa.toNat) (ram : NotMMIO pa)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (value : BitVec 64) (bytes : ∀ i < 8, s.mem[pa.toNat + i]? = some (value.extractLsb' (8 * i) 8)) :
    ∃ packet : ReadPacket ⟨offset,a,8,acc,aligned,ispair⟩ s, packet.data = value := by
  apply Payload.read8_natural_packet_value offset a acc aligned ispair natural s pa value hA post.noMTE2 ram
  intro u fu
  have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hA.gpr]; rfl
  rcases translation_facts spec config rows mapping ⟨offset,a,8,acc,aligned,ispair⟩ s
      member data current access mode post.post.aa64el0 debug post.post.spe notFetch dcache
      pa mapped raw none u fu with ⟨ad,t1,run,nf,paddr,wb,va,regs,mem,W,events⟩
  refine ⟨ad,t1,run,nf,paddr,wb.normal,wb.inner,wb.outer,?_,?_,W,?_,?_,events⟩
  · rw [regs]; exact post
  · intro i hi
    rw [mem]; exact bytes i hi
  · exact regs.trans fu.1.symm
  · exact mem.trans fu.2.1.symm


theorem read8_within16 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor) (aligned ispair : Bool) (s : State)
    (hlse : s.regs.FeatureImpl[111] = true) (fit : Read.Within16 a 8)
    (member : domain ⟨a,⟨acc,aligned⟩,((8 : Nat) : Int)⟩)
    (data : S1AccessData spec config rows ⟨a,⟨acc,aligned⟩,((8 : Nat) : Int)⟩)
    (current : CurrentS1At spec config rows s)
    (access : CurrentS1AccessAt spec config rows mapping
      ⟨a,⟨acc,aligned⟩,((8 : Nat) : Int)⟩ data s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs2 s.regs) (hA : AccDR2 acc) (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping a = some pa.toNat) (ram : NotMMIO pa)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (value : BitVec 64) (bytes : ∀ i < 8, s.mem[pa.toNat + i]? = some (value.extractLsb' (8 * i) 8)) :
    ∃ packet : ReadPacket ⟨offset,a,8,acc,aligned,ispair⟩ s, packet.data = value := by
  apply Payload.read8_within16_packet_value offset a acc aligned ispair s hlse fit pa value hA post.noMTE2 ram
  intro u fu
  have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hA.gpr]; rfl
  rcases translation_facts spec config rows mapping ⟨offset,a,8,acc,aligned,ispair⟩ s
      member data current access mode post.post.aa64el0 debug post.post.spe notFetch dcache
      pa mapped raw none u fu with ⟨ad,t1,run,nf,paddr,wb,va,regs,mem,W,events⟩
  refine ⟨ad,t1,run,nf,paddr,wb.normal,wb.inner,wb.outer,?_,?_,W,?_,?_,events⟩
  · rw [regs]; exact post
  · intro i hi
    rw [mem]; exact bytes i hi
  · exact regs.trans fu.1.symm
  · exact mem.trans fu.2.1.symm


theorem read16_natural {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor) (aligned ispair : Bool) (natural : a.toNat % 16 = 0) (s : State)
    (member : domain ⟨a,⟨acc,aligned⟩,((16 : Nat) : Int)⟩)
    (data : S1AccessData spec config rows ⟨a,⟨acc,aligned⟩,((16 : Nat) : Int)⟩)
    (current : CurrentS1At spec config rows s)
    (access : CurrentS1AccessAt spec config rows mapping
      ⟨a,⟨acc,aligned⟩,((16 : Nat) : Int)⟩ data s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs2 s.regs) (hA : AccDR2 acc) (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping a = some pa.toNat) (ram : NotMMIO pa)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (value : BitVec 128) (bytes : ∀ i < 16, s.mem[pa.toNat + i]? = some (value.extractLsb' (8 * i) 8)) :
    ∃ packet : ReadPacket ⟨offset,a,16,acc,aligned,ispair⟩ s, packet.data = value := by
  apply Payload.read16_natural_packet_value offset a acc aligned ispair natural s pa value hA post.noMTE2 ram
  intro u fu
  have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hA.gpr]; rfl
  rcases translation_facts spec config rows mapping ⟨offset,a,16,acc,aligned,ispair⟩ s
      member data current access mode post.post.aa64el0 debug post.post.spe notFetch dcache
      pa mapped raw none u fu with ⟨ad,t1,run,nf,paddr,wb,va,regs,mem,W,events⟩
  refine ⟨ad,t1,run,nf,paddr,wb.normal,wb.inner,wb.outer,?_,?_,W,?_,?_,events⟩
  · rw [regs]; exact post
  · intro i hi
    rw [mem]; exact bytes i hi
  · exact regs.trans fu.1.symm
  · exact mem.trans fu.2.1.symm


theorem read16_within16 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor) (aligned ispair : Bool) (s : State)
    (hlse : s.regs.FeatureImpl[111] = true) (fit : Read.Within16 a 16)
    (member : domain ⟨a,⟨acc,aligned⟩,((16 : Nat) : Int)⟩)
    (data : S1AccessData spec config rows ⟨a,⟨acc,aligned⟩,((16 : Nat) : Int)⟩)
    (current : CurrentS1At spec config rows s)
    (access : CurrentS1AccessAt spec config rows mapping
      ⟨a,⟨acc,aligned⟩,((16 : Nat) : Int)⟩ data s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs2 s.regs) (hA : AccDR2 acc) (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping a = some pa.toNat) (ram : NotMMIO pa)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (value : BitVec 128) (bytes : ∀ i < 16, s.mem[pa.toNat + i]? = some (value.extractLsb' (8 * i) 8)) :
    ∃ packet : ReadPacket ⟨offset,a,16,acc,aligned,ispair⟩ s, packet.data = value := by
  apply Payload.read16_within16_packet_value offset a acc aligned ispair s hlse fit pa value hA post.noMTE2 ram
  intro u fu
  have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hA.gpr]; rfl
  rcases translation_facts spec config rows mapping ⟨offset,a,16,acc,aligned,ispair⟩ s
      member data current access mode post.post.aa64el0 debug post.post.spe notFetch dcache
      pa mapped raw none u fu with ⟨ad,t1,run,nf,paddr,wb,va,regs,mem,W,events⟩
  refine ⟨ad,t1,run,nf,paddr,wb.normal,wb.inner,wb.outer,?_,?_,W,?_,?_,events⟩
  · rw [regs]; exact post
  · intro i hi
    rw [mem]; exact bytes i hi
  · exact regs.trans fu.1.symm
  · exact mem.trans fu.2.1.symm

/-- Actual store packet from current-query data and present control/image
facts; translation success is derived internally rather than admitted. -/
theorem write_natural {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (r : Access) (s : State) (hn : SizeOK r.bytes) (natural : r.va.toNat % r.bytes = 0)
    (member : domain ⟨r.va,⟨r.acc,r.aligned⟩,(r.bytes : Int)⟩)
    (data : S1AccessData spec config rows ⟨r.va,⟨r.acc,r.aligned⟩,(r.bytes : Int)⟩)
    (current : CurrentS1At spec config rows s)
    (access : CurrentS1AccessAt spec config rows mapping
      ⟨r.va,⟨r.acc,r.aligned⟩,(r.bytes : Int)⟩ data s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (hA : AccDWT r.acc) (tag : TagOK r.acc s.regs) (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping r.va = some pa.toNat) (ram : NotMMIO pa)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : NoUpdateRows {spec.params with haft := hostHAFT s.regs} r.acc spec.imageRows = true)
    (value : BitVec (r.bytes * 8)) :
    ∃ packet : WritePacket r s, packet.data = value := by
  apply Payload.write_natural_packet_value r s hn natural pa value hA tag ram
  intro u fu
  have notFetch : (r.acc.acctype == .AccessType_IFETCH) = false := by rw [hA.base.gpr]; rfl
  rcases translation_facts spec config rows mapping r s member data current access mode aa64 debug spe
      notFetch dcache pa mapped raw none u fu with
    ⟨ad,t1,run,nf,paddr,wb,va,regs,mem,W,events⟩
  refine ⟨ad,t1,run,nf,paddr,wb.normal,wb.inner,wb.outer,?_,?_,W,?_,?_,events⟩
  · rw [regs]; exact spe
  · rw [regs]; exact tag
  · exact regs.trans fu.1.symm
  · exact mem.trans fu.2.1.symm

/-- Actual store packet from current-query data and present control/image
facts; translation success is derived internally rather than admitted. -/
theorem write_within16 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (r : Access) (s : State) (hn : SizeOK r.bytes) (hlse : s.regs.FeatureImpl[111] = true) (fit : Read.Within16 r.va (r.bytes : Int))
    (member : domain ⟨r.va,⟨r.acc,r.aligned⟩,(r.bytes : Int)⟩)
    (data : S1AccessData spec config rows ⟨r.va,⟨r.acc,r.aligned⟩,(r.bytes : Int)⟩)
    (current : CurrentS1At spec config rows s)
    (access : CurrentS1AccessAt spec config rows mapping
      ⟨r.va,⟨r.acc,r.aligned⟩,(r.bytes : Int)⟩ data s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (hA : AccDWT r.acc) (tag : TagOK r.acc s.regs) (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping r.va = some pa.toNat) (ram : NotMMIO pa)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : NoUpdateRows {spec.params with haft := hostHAFT s.regs} r.acc spec.imageRows = true)
    (value : BitVec (r.bytes * 8)) :
    ∃ packet : WritePacket r s, packet.data = value := by
  apply Payload.write_within16_packet_value r s hn hlse fit pa value hA tag ram
  intro u fu
  have notFetch : (r.acc.acctype == .AccessType_IFETCH) = false := by rw [hA.base.gpr]; rfl
  rcases translation_facts spec config rows mapping r s member data current access mode aa64 debug spe
      notFetch dcache pa mapped raw none u fu with
    ⟨ad,t1,run,nf,paddr,wb,va,regs,mem,W,events⟩
  refine ⟨ad,t1,run,nf,paddr,wb.normal,wb.inner,wb.outer,?_,?_,W,?_,?_,events⟩
  · rw [regs]; exact spe
  · rw [regs]; exact tag
  · exact regs.trans fu.1.symm
  · exact mem.trans fu.2.1.symm

/-- Packet runs bind to the exact original Sail byte/half wrappers. -/
theorem read_wrapper {r : Access} {s : State} (packet : ReadPacket r s) (pair : r.ispair = false) :
    AArch64_MemSingle_read r.va r.bytes r.acc r.aligned s = .ok packet.data packet.after := by
  have run := packet.run
  unfold Access.read at run
  rw [pair] at run
  unfold AArch64_MemSingle_read
  simp only [Functor.map,EStateM.map,run,Sail.BitVec.castWidth_eq]

theorem write_wrapper {r : Access} {s : State} (packet : WritePacket r s) (pair : r.ispair = false) :
    AArch64_MemSingle_set r.va r.bytes r.acc r.aligned packet.data s = .ok () packet.after := by
  have run := packet.run
  unfold Access.write at run
  rw [pair] at run
  unfold AArch64_MemSingle_set
  simp only [Sail.BitVec.castWidth_eq,run]

#print axioms traffic_prefix
#print axioms translation_facts
#print axioms read8_natural
#print axioms read8_within16
#print axioms read16_natural
#print axioms read16_within16
#print axioms write_natural
#print axioms write_within16
#print axioms read_wrapper
#print axioms write_wrapper
#print axioms read_byte
end NativeAccess.Current
