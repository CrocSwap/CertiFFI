import NativeAccess.Plans
import ArmCertWalk.MemPairCore
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace NativeAccess.StoreLoops
open NativeAccess.Trace
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3 MemM1.MemWriteD5 MemM1.MemWriteD6
attribute [local implicit_reducible] EStateM Arch.arch_ak

/-- A past actual packet's exact physical write window, without logical
payload assumptions or a statement about any future execution. -/
theorem packet_frame {r : Access} {s : Trace.State} (packet : WritePacket r s) :
    WritesOnly (fun x => packet.ad.paddress.address.toNat ≤ x ∧
      x < packet.ad.paddress.address.toNat + r.bytes)
      (fun x => s.mem[x]?) (fun x => packet.after.mem[x]?) := by
  intro x outside
  rw [packet.memory]
  simp only [MemM1.MemWriteD1.wfold_get,outside,ite_false]

theorem current_after_packet {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {r : Access} {s : Trace.State}
    (current : CurrentS1At spec config rows s) (raw : RawImageAt spec.imageRows s.mem)
    (packet : WritePacket r s)
    (outside : ∀ i < r.bytes,
      ¬ (rowsFootprint spec.imageRows).byte (packet.ad.paddress.address.toNat + i)) :
    CurrentS1At spec config rows packet.after ∧ RawImageAt spec.imageRows packet.after.mem := by
  have separated : Separated (rowsFootprint spec.imageRows).byte
      (fun x => packet.ad.paddress.address.toNat ≤ x ∧
        x < packet.ad.paddress.address.toNat + r.bytes) := by
    intro x table ⟨lo,hi⟩
    have absent := outside (x - packet.ad.paddress.address.toNat) (by omega)
    rw [show packet.ad.paddress.address.toNat + (x - packet.ad.paddress.address.toNat) = x by omega] at absent
    exact absent table
  refine ⟨current_s1_program_write current _ (packet_frame packet) separated
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,
    raw_image_program_write raw _ (packet_frame packet) separated⟩
  all_goals (try intro _) <;> rw [packet.registers]

#print axioms packet_frame
#print axioms current_after_packet
theorem write_address {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (r : Access) (s : Trace.State)
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
    (packet : WritePacket r s) :
    packet.ad.paddress.address = pa ∧ packet.ad.vaddress = r.va := by
  rcases Current.translation_facts spec config rows mapping r s member data current access
      mode aa64 debug spe notFetch dcache pa mapped raw none packet.translationInput packet.choiceFrame with
    ⟨ad,t,run,nf,physical,normal,virtual,regs,mem,events⟩
  have same : packet.ad = ad := (EStateM.Result.ok.inj (packet.translation.symm.trans run)).1
  rw [same]
  exact ⟨physical,virtual⟩

#print axioms write_address

def writeBody (a : BitVec 64) (N : Nat) (acc : AccessDescriptor) (aligned : Bool)
    (value : BitVec (N * 8)) (i : Int) (_ : Unit) : SailM Unit :=
  AArch64_MemSingle_set (BitVec.addInt a i) 1 acc aligned
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb value
      (Sail.Int.toNatChecked (8 * i + 7)) (Sail.Int.toNatChecked (8 * i))))

def ByteWitness {N : Nat} (offsetBase start fuel : Nat) (a : BitVec 64)
    (acc : AccessDescriptor) (aligned : Bool) (value : BitVec (N * 8))
    (pa : Fin N → BitVec 56) (call : WriteCall) : Prop :=
  ∃ j : Fin N, start ≤ j.val ∧ j.val < start + fuel ∧
    call.request = Loops.byteAccess offsetBase a acc aligned j.val ∧
    call.packet.ad.paddress.address = pa j ∧
    (Sail.BitVec.castWidth call.packet.data : BitVec 8) = value.extractLsb' (8 * j.val) 8

/-- Actual byte stores derive their own past write chain and exact payloads.
The finite table-separation evidence is checked at each actual mapped byte. -/
theorem write_iterate {N : Nat} (small : N ≤ 16)
    (offsetBase : Nat) (a : BitVec 64) (acc : AccessDescriptor) (aligned : Bool)
    (value : BitVec (N * 8)) (hA : AccDWT acc)
    (domains : Fin N → QueryDomain) (specs : (j : Fin N) → TopologyImageSpec (domains j))
    (configs : Fin N → AttributeConfig) (rows : Fin N → List PermissionRow)
    (mapping : Fin N → BitVec 64 → Option Nat) (pa : Fin N → BitVec 56)
    (mapped : ∀ j : Fin N, mapping j (BitVec.addInt a (j.val : Int)) = some (pa j).toNat)
    (ram : ∀ j : Fin N, NotMMIO (pa j))
    (outside : ∀ j k : Fin N, ¬ (rowsFootprint (specs k).imageRows).byte (pa j).toNat)
    (start fuel : Nat) (bounded : start + fuel ≤ N) (s : Trace.State)
    (member : ∀ j : Fin N, domains j (Loops.byteQuery a acc aligned j.val))
    (data : ∀ j : Fin N, S1AccessData (specs j) (configs j) (rows j) (Loops.byteQuery a acc aligned j.val))
    (current : ∀ j : Fin N, CurrentS1At (specs j) (configs j) (rows j) s)
    (access : ∀ j : Fin N, CurrentS1AccessAt (specs j) (configs j) (rows j) (mapping j)
      (Loops.byteQuery a acc aligned j.val) (data j) s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (tag : TagOK acc s.regs) (dcache : currentDCache s.regs = true)
    (raw : ∀ j : Fin N, RawImageAt (specs j).imageRows s.mem)
    (none : ∀ j : Fin N,
      NoUpdateRows {(specs j).params with haft := hostHAFT s.regs} acc (specs j).imageRows = true) :
    ∃ (after : Trace.State) (calls : List WriteCall),
      Loops.iterate (writeBody a N acc aligned value) fuel (start : Int) () s = .ok () after ∧
      WriteChain s calls after ∧
      calls.map WriteCall.request = (List.range' start fuel).map (Loops.byteAccess offsetBase a acc aligned) ∧
      ∀ call ∈ calls, ByteWitness offsetBase start fuel a acc aligned value pa call := by
  induction fuel generalizing start s with
  | zero => exact ⟨s,[],rfl,.nil ⟨rfl,rfl,rfl⟩,rfl,by simp⟩
  | succ fuel ih =>
    let j : Fin N := ⟨start,by omega⟩
    let r := Loops.byteAccess offsetBase a acc aligned start
    rcases Current.write_natural (specs j) (configs j) (rows j) (mapping j) r s
        (Or.inl rfl) (Nat.mod_one _) (member j) (data j) (current j) (access j)
        mode aa64 debug spe hA tag dcache (pa j) (mapped j) (ram j) (raw j) (none j)
        (value.extractLsb' (8 * start) 8) with ⟨packet,payload⟩
    have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hA.base.gpr]; rfl
    have address := write_address (specs j) (configs j) (rows j) (mapping j) r s
      (member j) (data j) (current j) (access j) mode aa64 debug spe notFetch dcache
      (pa j) (mapped j) (raw j) (none j) packet
    have preserved : ∀ k : Fin N, CurrentS1At (specs k) (configs k) (rows k) packet.after ∧
        RawImageAt (specs k).imageRows packet.after.mem := by
      intro k
      apply current_after_packet (current k) (raw k) packet
      intro i hi
      have iz : i = 0 := by change i < 1 at hi; omega
      subst i
      rw [address.1,Nat.add_zero]
      exact outside j k
    have first := Current.write_wrapper packet rfl
    rw [payload] at first
    have body : writeBody a N acc aligned value (start : Int) () s = .ok () packet.after := by
      unfold writeBody
      rw [Bytes.sail_byte_int _ _ (by omega)]
      simpa [r,Loops.byteAccess] using first
    have rest := ih (start := start + 1) (s := packet.after) (bounded := by omega)
      (current := fun k => (preserved k).1)
      (access := fun k => (access k).of_regs packet.registers)
      (mode := by rw [packet.registers]; exact mode)
      (aa64 := by rw [packet.registers]; exact aa64)
      (debug := by rw [packet.registers]; exact debug)
      (spe := by rw [packet.registers]; exact spe)
      (tag := by rw [packet.registers]; exact tag)
      (dcache := by rw [packet.registers]; exact dcache)
      (raw := fun k => (preserved k).2)
      (none := by intro k; rw [packet.registers]; exact none k)
    rcases rest with ⟨after,calls,run,chain,requests,witness⟩
    let call : WriteCall := ⟨r,s,packet⟩
    refine ⟨after,call :: calls,?_,.cons call ⟨rfl,rfl,rfl⟩ chain,?_,?_⟩
    · have cursor : (start : Int) + 1 = ((start + 1 : Nat) : Int) := by omega
      simp only [Loops.iterate,Bind.bind,EStateM.bind,body,cursor,run]
    · change Loops.byteAccess offsetBase a acc aligned start :: calls.map WriteCall.request = _
      rw [List.range'_succ,List.map_cons,requests]
    · intro c memberC
      rcases List.mem_cons.mp memberC with rfl | inside
      · refine ⟨j,by dsimp [j]; omega,by dsimp [j]; omega,rfl,address.1,?_⟩
        change (Sail.BitVec.castWidth packet.data : BitVec 8) = _
        rw [payload]
        exact Sail.BitVec.castWidth_eq _
      · obtain ⟨k,lo,hi,request,physical,bytes⟩ := witness c inside
        exact ⟨k,by omega,by omega,request,physical,bytes⟩

#print axioms write_iterate
theorem write_range {N : Nat} (small : N ≤ 16)
    (offsetBase : Nat) (a : BitVec 64) (acc : AccessDescriptor) (aligned : Bool)
    (value : BitVec (N * 8)) (hA : AccDWT acc)
    (domains : Fin N → QueryDomain) (specs : (j : Fin N) → TopologyImageSpec (domains j))
    (configs : Fin N → AttributeConfig) (rows : Fin N → List PermissionRow)
    (mapping : Fin N → BitVec 64 → Option Nat) (pa : Fin N → BitVec 56)
    (mapped : ∀ j : Fin N, mapping j (BitVec.addInt a (j.val : Int)) = some (pa j).toNat)
    (ram : ∀ j : Fin N, NotMMIO (pa j))
    (outside : ∀ j k : Fin N, ¬ (rowsFootprint (specs k).imageRows).byte (pa j).toNat)
    (start fuel : Nat) (bounded : start + fuel ≤ N) (s : Trace.State)
    (member : ∀ j : Fin N, domains j (Loops.byteQuery a acc aligned j.val))
    (data : ∀ j : Fin N, S1AccessData (specs j) (configs j) (rows j) (Loops.byteQuery a acc aligned j.val))
    (current : ∀ j : Fin N, CurrentS1At (specs j) (configs j) (rows j) s)
    (access : ∀ j : Fin N, CurrentS1AccessAt (specs j) (configs j) (rows j) (mapping j)
      (Loops.byteQuery a acc aligned j.val) (data j) s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (tag : TagOK acc s.regs) (dcache : currentDCache s.regs = true)
    (raw : ∀ j : Fin N, RawImageAt (specs j).imageRows s.mem)
    (none : ∀ j : Fin N,
      NoUpdateRows {(specs j).params with haft := hostHAFT s.regs} acc (specs j).imageRows = true) :
    ∃ (after : Trace.State) (calls : List WriteCall),
      (forIn ({start := (start : Int),stop := (start : Int) + (fuel : Int) - 1,step := 1} : IntRange)
        () (fun i u => do let next ← writeBody a N acc aligned value i u; pure (.yield next)) : SailM Unit) s = .ok () after ∧
      WriteChain s calls after ∧
      calls.map WriteCall.request = (List.range' start fuel).map (Loops.byteAccess offsetBase a acc aligned) ∧
      ∀ call ∈ calls, ByteWitness offsetBase start fuel a acc aligned value pa call := by
  rcases write_iterate small offsetBase a acc aligned value hA domains specs configs rows mapping pa
      mapped ram outside start fuel bounded s member data current access mode aa64 debug spe tag dcache raw none with
    ⟨after,calls,run,chain,requests,witness⟩
  refine ⟨after,calls,?_,chain,requests,witness⟩
  rw [Loops.range_eq_iterate]
  exact run

#print axioms write_range

theorem chain_prepend {s u t : Trace.State} {calls : List WriteCall}
    (frame : Frame s u) (chain : WriteChain u calls t) : WriteChain s calls t := by
  cases chain with
  | nil f => exact .nil (frame_trans frame f)
  | cons c f tail => exact .cons c (frame_trans frame f) tail

theorem chain_append {s u t : Trace.State} {left right : List WriteCall}
    (first : WriteChain s left u) (second : WriteChain u right t) : WriteChain s (left ++ right) t := by
  induction first with
  | nil f => exact chain_prepend f second
  | cons c f tail ih => exact .cons c f (ih second)

theorem current_after_byteChain {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {s t : Trace.State}
    {calls : List WriteCall} {N : Nat} {offsetBase start fuel : Nat}
    {a : BitVec 64} {acc : AccessDescriptor} {aligned : Bool} {value : BitVec (N * 8)}
    {pa : Fin N → BitVec 56}
    (current : CurrentS1At spec config rows s) (raw : RawImageAt spec.imageRows s.mem)
    (chain : WriteChain s calls t)
    (witness : ∀ c ∈ calls, ByteWitness offsetBase start fuel a acc aligned value pa c)
    (outside : ∀ j : Fin N, ¬ (rowsFootprint spec.imageRows).byte (pa j).toNat) :
    CurrentS1At spec config rows t ∧ RawImageAt spec.imageRows t.mem := by
  induction chain with
  | nil frame =>
    refine ⟨current_s1_frame current frame.1 frame.2.1,?_⟩
    rw [frame.2.1]; exact raw
  | cons c frame tail ih =>
    obtain ⟨j,lo,hi,request,physical,payload⟩ := witness c (by simp)
    have before := current_s1_frame current frame.1 frame.2.1
    have beforeRaw : RawImageAt spec.imageRows c.before.mem := by rw [frame.2.1]; exact raw
    have next := current_after_packet before beforeRaw c.packet (by
      intro i bound
      have iz : i = 0 := by rw [request] at bound; change i < 1 at bound; omega
      subst i
      rw [physical,Nat.add_zero]
      exact outside j)
    exact ih next.1 next.2 (fun k member => witness k (List.mem_cons_of_mem _ member))

#print axioms current_after_byteChain

def storePrefix (a : BitVec 64) (N : Nat) (acc : AccessDescriptor)
    (value : BitVec (N * 8)) : SailM (BitVec (N * 8)) := do
  let _ ← undefined_Constraint (← occLabel 1646) ()
  let _ ← undefined_bool_at (← occLabel 1647) ()
  let _ ← AArch64_UnalignedAccessFaults acc a (N : Int)
  let be ← BigEndian acc.acctype
  let value := if be then reverse_endianness value else value
  let h := Sail.Int.toNatChecked (Int.ediv (N : Int) 2)
  let _ ← undefined_bitvector_at (← occLabel 1648) (Sail.Int.toNatChecked (h *i 8))
  let _ ← undefined_bitvector_at (← occLabel 1649) (Sail.Int.toNatChecked (h *i 8))
  let _ ← HaveLRCPC3Ext ()
  pure value

theorem storePrefix_run (a : BitVec 64) (N : Nat) (acc : AccessDescriptor)
    (value : BitVec (N * 8)) (s : Trace.State) (host : HostPins s)
    (disabled : _get_SCTLR_EL2_Type_A (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1)
    (plain : Plain acc) (hA : AccDWT acc) (pre : PreW acc s.regs) :
    ∃ t, storePrefix a N acc value s = .ok value t ∧ Frame s t := by
  rcases occ_normal 1646 s with ⟨l1,s1,e1,f1⟩
  rcases constraint_normal l1 s1 with ⟨c,s2,e2,f2⟩
  rcases occ_normal 1647 s2 with ⟨l2,s3,e3,f3⟩
  rcases S1EntryCalleesExtra.bool_normal l2 s3 with ⟨b,s4,e4,f4⟩
  have F4 := frame_trans (frame_trans (frame_trans f1 f2) f3) f4
  have host4 : HostPins s4 := by
    rcases host with ⟨el,nrw,aa,rme,vhe,ns,e2h,tge⟩
    constructor <;> rw [F4.1] <;> assumption
  rcases plain_unaligned_allowed s4 host4 (by rw [F4.1]; exact disabled) acc plain a (N : Int) with
    ⟨s5,ef,rf,mf,vf⟩
  have F5 := frame_trans F4 ⟨rf,mf,vf⟩
  rcases littleEndian_of acc s hA pre s5 F5 with ⟨s6,eb,fb⟩
  let h := Sail.Int.toNatChecked (Int.ediv (N : Int) 2)
  rcases occ_normal 1648 s6 with ⟨l3,s7,e7,f7⟩
  rcases bits_normal (Sail.Int.toNatChecked (h *i 8)) l3 s7 with ⟨b1,s8,e8,f8⟩
  rcases occ_normal 1649 s8 with ⟨l4,s9,e9,f9⟩
  rcases bits_normal (Sail.Int.toNatChecked (h *i 8)) l4 s9 with ⟨b2,s10,e10,f10⟩
  have ext : HaveLRCPC3Ext () s10 = .ok s10.regs.FeatureImpl[190] s10 := rfl
  refine ⟨s10,?_,frame_trans (frame_trans (frame_trans (frame_trans (frame_trans F5 fb) f7) f8) f9) f10⟩
  dsimp only [h] at e8 e10
  simp only [storePrefix,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
    e1,e2,e3,e4,ef,eb,e7,e8,e9,e10,ext,Bool.false_eq_true,ite_false]

def storeSuffix (a : BitVec 64) (N : Nat) (acc : AccessDescriptor)
    (value : BitVec (N * 8)) : SailM Unit := do
  writeBody a N acc false value 0 ()
  let c ← ConstrainUnpredictable .Unpredictable_DEVPAGE2
  let aligned := c == Constraint.Constraint_NONE
  forIn ({start := 1,stop := N -i 1,step := 1} : IntRange) ()
    (fun i u => do let next ← writeBody a N acc aligned value i u; pure (.yield next))

theorem storePlan_eq (a : BitVec 64) (N : Nat) (acc : AccessDescriptor)
    (value : BitVec (N * 8)) : Logical.store_bytePlan a N acc value = (do
      let value ← storePrefix a N acc value
      storeSuffix a N acc value) := by
  simp [Logical.store_bytePlan,storePrefix,storeSuffix,writeBody,BitVec.addInt,
    Sail.Int.toNatChecked,Sail.BitVec.castWidth_eq,bind_assoc]

#print axioms storePrefix_run
#print axioms storePlan_eq
theorem storeSuffix_run {N : Nat} (positive : 0 < N) (small : N ≤ 16)
    (offsetBase : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (value : BitVec (N * 8)) (hA : AccDWT acc)
    (domains : Fin N → BitVec 64 → Prop)
    (specs : (j : Fin N) → TopologyImageSpec (fun q => domains j q.va))
    (configs : Fin N → AttributeConfig) (rows : Fin N → List PermissionRow)
    (mapping : Fin N → BitVec 64 → Option Nat) (pa : Fin N → BitVec 56)
    (mapped : ∀ j : Fin N, mapping j (BitVec.addInt a (j.val : Int)) = some (pa j).toNat)
    (ram : ∀ j : Fin N, NotMMIO (pa j))
    (outside : ∀ j k : Fin N, ¬ (rowsFootprint (specs k).imageRows).byte (pa j).toNat)
    (s : Trace.State)
    (member : ∀ j : Fin N, domains j (BitVec.addInt a (j.val : Int)))
    (data : ∀ j : Fin N, S1AccessData (specs j) (configs j) (rows j) (Loops.byteQuery a acc false j.val))
    (current : ∀ j : Fin N, CurrentS1At (specs j) (configs j) (rows j) s)
    (access : ∀ j : Fin N, CurrentS1AccessAt (specs j) (configs j) (rows j) (mapping j)
      (Loops.byteQuery a acc false j.val) (data j) s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (tag : TagOK acc s.regs) (dcache : currentDCache s.regs = true)
    (raw : ∀ j : Fin N, RawImageAt (specs j).imageRows s.mem)
    (none : ∀ j : Fin N,
      NoUpdateRows {(specs j).params with haft := hostHAFT s.regs} acc (specs j).imageRows = true) :
    ∃ (after : Trace.State) (calls : List WriteCall) (aligned : Bool),
      storeSuffix a N acc value s = .ok () after ∧ WriteChain s calls after ∧
      calls.map WriteCall.request = Loops.byteAccess offsetBase a acc false 0 ::
        (List.range' 1 (N - 1)).map (Loops.byteAccess offsetBase a acc aligned) ∧
      ∀ call ∈ calls, ByteWitness offsetBase 0 1 a acc false value pa call ∨
        ByteWitness offsetBase 1 (N - 1) a acc aligned value pa call := by
  rcases write_iterate small offsetBase a acc false value hA (fun j q => domains j q.va)
      specs configs rows mapping pa mapped ram outside 0 1 (by omega) s member data current access
      mode aa64 debug spe tag dcache raw none with
    ⟨s1,firstCalls,firstRun,firstChain,firstRequests,firstWitness⟩
  have firstBody : writeBody a N acc false value 0 () s = .ok () s1 := by
    simpa [Loops.iterate] using firstRun
  rcases Logical.devpage_allowed s1 with ⟨c,s2,choice,allowed,choiceFrame⟩
  let aligned := c == Constraint.Constraint_NONE
  have preserved : ∀ k : Fin N, CurrentS1At (specs k) (configs k) (rows k) s1 ∧
      RawImageAt (specs k).imageRows s1.mem := by
    intro k
    exact current_after_byteChain (current k) (raw k) firstChain firstWitness (fun j => outside j k)
  have regs : s2.regs = s.regs := choiceFrame.1.trans firstChain.registers
  rcases write_range small offsetBase a acc aligned value hA (fun j q => domains j q.va)
      specs configs rows mapping pa mapped ram outside 1 (N - 1) (by omega) s2 member
      (fun j => Plans.data_reflag (data j) aligned)
      (fun k => current_s1_frame (preserved k).1 choiceFrame.1 choiceFrame.2.1)
      (fun k => (Plans.access_reflag (access k) aligned).of_regs regs)
      (by rw [regs]; exact mode) (by rw [regs]; exact aa64)
      (by rw [regs]; exact debug) (by rw [regs]; exact spe)
      (by rw [regs]; exact tag) (by rw [regs]; exact dcache)
      (by intro k; rw [choiceFrame.2.1]; exact (preserved k).2)
      (by intro k; rw [regs]; exact none k) with
    ⟨s3,tailCalls,tailRun,tailChain,tailRequests,tailWitness⟩
  refine ⟨s3,firstCalls ++ tailCalls,aligned,?_,
    chain_append firstChain (chain_prepend choiceFrame tailChain),?_,?_⟩
  · have one : ((1 : Nat) : Int) = 1 := by decide
    simp only [one] at tailRun
    have stop : (N : Int) - 1 = (1 : Int) + ((N - 1 : Nat) : Int) - 1 := by omega
    unfold storeSuffix
    simp only [Bind.bind,EStateM.bind,firstBody,choice]
    rw [stop]
    exact tailRun
  · rw [List.map_append,firstRequests,tailRequests]
    rfl
  · intro call memberCall
    rcases List.mem_append.mp memberCall with left | right
    · exact Or.inl (firstWitness call left)
    · exact Or.inr (tailWitness call right)

#print axioms storeSuffix_run
theorem storePlan_run {N : Nat} (positive : 0 < N) (small : N ≤ 16)
    (offsetBase : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (value : BitVec (N * 8)) (hA : AccDWT acc)
    (domains : Fin N → BitVec 64 → Prop)
    (specs : (j : Fin N) → TopologyImageSpec (fun q => domains j q.va))
    (configs : Fin N → AttributeConfig) (rows : Fin N → List PermissionRow)
    (mapping : Fin N → BitVec 64 → Option Nat) (pa : Fin N → BitVec 56)
    (mapped : ∀ j : Fin N, mapping j (BitVec.addInt a (j.val : Int)) = some (pa j).toNat)
    (ram : ∀ j : Fin N, NotMMIO (pa j))
    (outside : ∀ j k : Fin N, ¬ (rowsFootprint (specs k).imageRows).byte (pa j).toNat)
    (s : Trace.State)
    (host : HostPins s)
    (disabled : _get_SCTLR_EL2_Type_A (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1)
    (plain : Plain acc) (pre : PreW acc s.regs)
    (member : ∀ j : Fin N, domains j (BitVec.addInt a (j.val : Int)))
    (data : ∀ j : Fin N, S1AccessData (specs j) (configs j) (rows j) (Loops.byteQuery a acc false j.val))
    (current : ∀ j : Fin N, CurrentS1At (specs j) (configs j) (rows j) s)
    (access : ∀ j : Fin N, CurrentS1AccessAt (specs j) (configs j) (rows j) (mapping j)
      (Loops.byteQuery a acc false j.val) (data j) s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (tag : TagOK acc s.regs) (dcache : currentDCache s.regs = true)
    (raw : ∀ j : Fin N, RawImageAt (specs j).imageRows s.mem)
    (none : ∀ j : Fin N,
      NoUpdateRows {(specs j).params with haft := hostHAFT s.regs} acc (specs j).imageRows = true) :
    ∃ (after : Trace.State) (calls : List WriteCall) (aligned : Bool),
      Logical.store_bytePlan a N acc value s = .ok () after ∧ WriteChain s calls after ∧
      calls.map WriteCall.request = Loops.byteAccess offsetBase a acc false 0 ::
        (List.range' 1 (N - 1)).map (Loops.byteAccess offsetBase a acc aligned) ∧
      ∀ call ∈ calls, ByteWitness offsetBase 0 1 a acc false value pa call ∨
        ByteWitness offsetBase 1 (N - 1) a acc aligned value pa call := by
  rcases storePrefix_run a N acc value s host disabled plain hA pre with ⟨u,preRun,frame⟩
  rcases storeSuffix_run positive small offsetBase a acc value hA domains specs configs rows mapping pa
      mapped ram outside u member data
      (fun j => current_s1_frame (current j) frame.1 frame.2.1)
      (fun j => (access j).of_regs frame.1)
      (by rw [frame.1]; exact mode) (by rw [frame.1]; exact aa64)
      (by rw [frame.1]; exact debug) (by rw [frame.1]; exact spe)
      (by rw [frame.1]; exact tag) (by rw [frame.1]; exact dcache)
      (by intro j; rw [frame.2.1]; exact raw j)
      (by intro j; rw [frame.1]; exact none j) with
    ⟨after,calls,aligned,run,chain,requests,witness⟩
  refine ⟨after,calls,aligned,?_,chain_prepend frame chain,requests,witness⟩
  rw [storePlan_eq]
  simp only [Bind.bind,EStateM.bind,preRun,run]

#print axioms storePlan_run
theorem store_bytes_low_order {N : Nat} (hn : N = 8 ∨ N = 16)
    (offsetBase : Nat) (a : BitVec 64) (acc : AccessDescriptor) (pair high : Bool)
    (unaligned : Logical.accessAligned a N pair = false)
    (value : BitVec (N * 8)) (hA : AccDWT acc)
    (domains : Fin N → BitVec 64 → Prop)
    (specs : (j : Fin N) → TopologyImageSpec (fun q => domains j q.va))
    (configs : Fin N → AttributeConfig) (rows : Fin N → List PermissionRow)
    (mapping : Fin N → BitVec 64 → Option Nat) (pa : Fin N → BitVec 56)
    (mapped : ∀ j : Fin N, mapping j (BitVec.addInt a (j.val : Int)) = some (pa j).toNat)
    (ram : ∀ j : Fin N, NotMMIO (pa j))
    (outside : ∀ j k : Fin N, ¬ (rowsFootprint (specs k).imageRows).byte (pa j).toNat)
    (s : Trace.State)
    (profile : AccessProfile) (pins : ProfileAt profile s)
    (notJoin : (s.regs.FeatureImpl[111] &&
      (Align_bits (BitVec.subInt (BitVec.addInt a (N : Int)) 1) 16 == Align_bits a 16)) = false)
    (lowOrder : ((s.regs.FeatureImpl[190] && pair) && high) = false)
    (plain : Plain acc) (pre : PreW acc s.regs)
    (member : ∀ j : Fin N, domains j (BitVec.addInt a (j.val : Int)))
    (data : ∀ j : Fin N, S1AccessData (specs j) (configs j) (rows j) (Loops.byteQuery a acc false j.val))
    (current : ∀ j : Fin N, CurrentS1At (specs j) (configs j) (rows j) s)
    (access : ∀ j : Fin N, CurrentS1AccessAt (specs j) (configs j) (rows j) (mapping j)
      (Loops.byteQuery a acc false j.val) (data j) s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (tag : TagOK acc s.regs) (dcache : currentDCache s.regs = true)
    (raw : ∀ j : Fin N, RawImageAt (specs j).imageRows s.mem)
    (none : ∀ j : Fin N,
      NoUpdateRows {(specs j).params with haft := hostHAFT s.regs} acc (specs j).imageRows = true) :
    ∃ (after : Trace.State) (calls : List WriteCall) (aligned : Bool),
      Mem_set__2 a N acc pair high value s = .ok () after ∧ WriteChain s calls after ∧
      calls.map WriteCall.request = Loops.byteAccess offsetBase a acc false 0 ::
        (List.range' 1 (N - 1)).map (Loops.byteAccess offsetBase a acc aligned) ∧
      ∀ call ∈ calls, ByteWitness offsetBase 0 1 a acc false value pa call ∨
        ByteWitness offsetBase 1 (N - 1) a acc aligned value pa call := by
  have positive : 0 < N := by rcases hn with rfl | rfl <;> omega
  have small : N ≤ 16 := by rcases hn with rfl | rfl <;> omega
  rcases storePlan_run positive small offsetBase a acc value hA domains specs configs rows mapping pa
      mapped ram outside s pins.host pins.alignment_disabled plain pre member data current access mode aa64
      debug spe tag dcache raw none with ⟨after,calls,aligned,run,chain,requests,witness⟩
  refine ⟨after,calls,aligned,?_,chain,requests,witness⟩
  rw [Logical.store_bytes_low_order a N hn pair high unaligned acc hA plain value s profile pins pre notJoin lowOrder]
  exact run

#print axioms store_bytes_low_order
end NativeAccess.StoreLoops
