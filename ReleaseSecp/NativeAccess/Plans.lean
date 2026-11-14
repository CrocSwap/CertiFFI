import NativeAccess.Loops
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace NativeAccess.Plans
attribute [local implicit_reducible] EStateM Arch.arch_ak
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open NativeAccess.Trace

/-- Changing the actual alignment flag does not change the static path or
permission evidence. Domain membership remains a separate obligation. -/
def reflag (q : AccessQuery) (aligned : Bool) : AccessQuery :=
  ⟨q.va,⟨q.request.raw,aligned⟩,q.size⟩

def data_reflag {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {q : AccessQuery}
    (data : S1AccessData spec config rows q) (aligned : Bool) :
    S1AccessData spec config rows (reflag q aligned) where
  leafLevel := data.leafLevel
  logical := data.logical
  physical := data.physical
  view := data.view
  path := data.path
  permissions := ⟨data.permissions.row,data.permissions.member,data.permissions.slot,
    data.permissions.words,data.permissions.annotation,data.permissions.used,
    data.permissions.rowView,data.permissions.attributes,data.permissions.kind,
    data.permissions.read,data.permissions.write,data.permissions.tagaccess⟩
  lower := data.lower
  accessEL := data.accessEL
  nonsecure := data.nonsecure

theorem access_reflag {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {q : AccessQuery}
    {mapping : BitVec 64 → Option Nat} {s : Loops.State}
    {data : S1AccessData spec config rows q}
    (access : CurrentS1AccessAt spec config rows mapping q data s) (aligned : Bool) :
    CurrentS1AccessAt spec config rows mapping (reflag q aligned) (data_reflag data aligned) s := by
  exact ⟨access.layout,access.checks,access.epd,
    ⟨access.map.mapped,access.map.admissible⟩,access.outputPolicy⟩

#print axioms data_reflag
#print axioms access_reflag

/-- The actual control/undefined prefix before the first physical byte read. -/
def readPrefix (a : BitVec 64) (n : Nat) (acc : AccessDescriptor) : SailM (BitVec (n * 8)) := do
  let _ ← undefined_Constraint (← occLabel 1640) ()
  let v : BitVec (n * 8) ← Sail.BitVec.castWidth <$> undefined_bitvector_at (← occLabel 1641)
    (Sail.Int.toNatChecked (n *i 8))
  let _ ← AArch64_UnalignedAccessFaults acc a (n : Int)
  let h := Sail.Int.toNatChecked (Int.ediv (n : Int) 2)
  let _ ← undefined_bitvector_at (← occLabel 1642) (Sail.Int.toNatChecked (h *i 8))
  let _ ← undefined_bitvector_at (← occLabel 1643) (Sail.Int.toNatChecked (h *i 8))
  let _ ← HaveLRCPC3Ext ()
  pure v

theorem readPrefix_run (a : BitVec 64) (n : Nat) (acc : AccessDescriptor)
    (s : Loops.State) (host : HostPins s)
    (disabled : _get_SCTLR_EL2_Type_A (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1)
    (plain : Plain acc) :
    ∃ v t, readPrefix a n acc s = .ok v t ∧ Frame s t := by
  rcases occ_normal 1640 s with ⟨l1,s1,e1,f1⟩
  obtain ⟨c,e2⟩ := constraint_ok l1 s1
  rcases occ_normal 1641 s1 with ⟨l2,s2,e3,f2⟩
  have width : Sail.Int.toNatChecked (n *i 8) = n * 8 := by
    simpa using Logical.checked_nat (n * 8)
  change Sail.Int.toNatChecked ((n : Int) * 8) = n * 8 at width
  rcases bits_normal (n * 8) l2 s2 with ⟨v,s3,e4,f3⟩
  have f03 := frame_trans (frame_trans f1 f2) f3
  have host3 : HostPins s3 := by
    rcases host with ⟨el,nrw,aa,rme,vhe,ns,e2h,tge⟩
    constructor <;> rw [f03.1] <;> assumption
  obtain ⟨s4,ef,rf,mf,vf⟩ := plain_unaligned_allowed s3 host3
    (by rw [f03.1]; exact disabled) acc plain a (n : Int)
  let h := Sail.Int.toNatChecked (Int.ediv (n : Int) 2)
  rcases occ_normal 1642 s4 with ⟨l3,s5,e5,f5⟩
  rcases bits_normal (Sail.Int.toNatChecked (h *i 8)) l3 s5 with ⟨b1,s6,e6,f6⟩
  rcases occ_normal 1643 s6 with ⟨l4,s7,e7,f7⟩
  rcases bits_normal (Sail.Int.toNatChecked (h *i 8)) l4 s7 with ⟨b2,s8,e8,f8⟩
  have ext : HaveLRCPC3Ext () s8 = .ok s8.regs.FeatureImpl[190] s8 := rfl
  refine ⟨v,s8,?_,frame_trans (frame_trans (frame_trans (frame_trans
    (frame_trans f03 ⟨rf,mf,vf⟩) f5) f6) f7) f8⟩
  dsimp only [h] at e6 e8
  simp only [readPrefix]
  rw [width]
  simp only [Functor.map,EStateM.map,Bind.bind,EStateM.bind,
    Pure.pure,EStateM.pure,e1,e2,e3,e4,ef,e5,e6,e7,e8,ext,Sail.BitVec.castWidth_eq]

#print axioms readPrefix_run

def readSuffix (a : BitVec 64) (n : Nat) (acc : AccessDescriptor)
    (v : BitVec (n * 8)) : SailM (BitVec (n * 8)) := do
  let b ← AArch64_MemSingle_read a 1 acc false
  let v := Sail.BitVec.updateSubrange v 7 0 b
  let c ← ConstrainUnpredictable .Unpredictable_DEVPAGE2
  let aligned := c == Constraint.Constraint_NONE
  let mut loop_vars := v
  for i in [1:(Sail.Int.toNatChecked (n -i 1)):1]i do
    loop_vars ← Loops.readBody a n acc aligned i loop_vars
  let be ← BigEndian acc.acctype
  pure (if be then reverse_endianness loop_vars else loop_vars)

theorem readPlan_eq (a : BitVec 64) (n : Nat) (acc : AccessDescriptor) :
    Logical.read_bytePlan a n acc = (do
      let v ← readPrefix a n acc
      readSuffix a n acc v) := by
  simp only [Logical.read_bytePlan,readPrefix,readSuffix,Loops.readBody,bind_assoc,pure_bind]

#print axioms readPlan_eq

theorem readSuffix_body (a : BitVec 64) (n : Nat) (acc : AccessDescriptor)
    (v : BitVec (n * 8)) : readSuffix a n acc v = (do
      let v ← Loops.readBody a n acc false 0 v
      let c ← ConstrainUnpredictable .Unpredictable_DEVPAGE2
      let aligned := c == Constraint.Constraint_NONE
      let mut loop_vars := v
      for i in [1:(Sail.Int.toNatChecked (n -i 1)):1]i do
        loop_vars ← Loops.readBody a n acc aligned i loop_vars
      let be ← BigEndian acc.acctype
      pure (if be then reverse_endianness loop_vars else loop_vars)) := by
  simp [readSuffix,Loops.readBody,BitVec.addInt,Sail.Int.toNatChecked,Sail.BitVec.castWidth_eq]

#print axioms readSuffix_body

/-- Actual first-byte/DEVPAGE2/tail execution. Coverage is a VA-keyed topology
envelope; only the selected alignment flags occur in the derived request list. -/
theorem readSuffix_run {N : Nat} (positive : 0 < N) (small : N ≤ 16)
    (offsetBase : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (initial target : BitVec (N * 8)) (hA : AccDR2 acc)
    (domains : Fin N → BitVec 64 → Prop)
    (specs : (j : Fin N) → TopologyImageSpec (fun q => domains j q.va))
    (configs : Fin N → AttributeConfig) (rows : Fin N → List PermissionRow)
    (mapping : Fin N → BitVec 64 → Option Nat) (pa : Fin N → BitVec 56)
    (mapped : ∀ j : Fin N, mapping j (BitVec.addInt a (j.val : Int)) = some (pa j).toNat)
    (ram : ∀ j : Fin N, NotMMIO (pa j)) (s : Loops.State)
    (member : ∀ j : Fin N, domains j (BitVec.addInt a (j.val : Int)))
    (data : ∀ j : Fin N, S1AccessData (specs j) (configs j) (rows j)
      (Loops.byteQuery a acc false j.val))
    (current : ∀ j : Fin N, CurrentS1At (specs j) (configs j) (rows j) s)
    (access : ∀ j : Fin N, CurrentS1AccessAt (specs j) (configs j) (rows j) (mapping j)
      (Loops.byteQuery a acc false j.val) (data j) s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs2 s.regs) (dcache : currentDCache s.regs = true)
    (raw : ∀ j : Fin N, RawImageAt (specs j).imageRows s.mem)
    (none : ∀ j : Fin N,
      NoUpdateRows {(specs j).params with haft := hostHAFT s.regs} acc (specs j).imageRows = true)
    (bytes : ∀ j : Fin N, s.mem[(pa j).toNat]? = some (target.extractLsb' (8 * j.val) 8)) :
    ∃ (after : Loops.State) (calls : List ReadCall) (aligned : Bool),
      readSuffix a N acc initial s = .ok target after ∧ ReadChain s calls after ∧
      calls.map ReadCall.request =
        Loops.byteAccess offsetBase a acc false 0 ::
          (List.range' 1 (N - 1)).map (Loops.byteAccess offsetBase a acc aligned) := by
  rcases Loops.read_iterate small offsetBase a acc false initial target hA
      (fun j q => domains j q.va) specs configs rows mapping pa mapped ram 0 1 (by omega) s
      (fun j _ _ => member j) (fun j _ _ => data j) (fun j _ _ => current j)
      (fun j _ _ => access j) mode debug post dcache
      (fun j _ _ => raw j) (fun j _ _ => none j) (fun j _ _ => bytes j) with
    ⟨s1,firstCalls,firstRun,firstChain,firstRequests⟩
  have firstBody : Loops.readBody a N acc false 0 initial s =
      .ok (Bytes.fill initial target 1) s1 := by
    simpa [Loops.iterate,Bytes.fill] using firstRun
  rcases Logical.devpage_allowed s1 with ⟨c,s2,choice,allowed,choiceFrame⟩
  let aligned := c == Constraint.Constraint_NONE
  have regs : s2.regs = s.regs := choiceFrame.1.trans firstChain.registers
  have mem : s2.mem = s.mem := choiceFrame.2.1.trans firstChain.memory
  rcases Loops.read_range small offsetBase a acc aligned initial target hA
      (fun j q => domains j q.va) specs configs rows mapping pa mapped ram 1 (N - 1) (by omega) s2
      (fun j _ _ => member j)
      (fun j _ _ => data_reflag (data j) aligned)
      (fun j _ _ => current_s1_frame (current j) regs mem)
      (fun j _ _ => (access_reflag (access j) aligned).of_regs regs)
      (by rw [regs]; exact mode) (by rw [regs]; exact debug)
      (by rw [regs]; exact post) (by rw [regs]; exact dcache)
      (by intro j _ _; rw [mem]; exact raw j)
      (by intro j _ _; rw [regs]; exact none j)
      (by intro j _ _; rw [mem]; exact bytes j) with
    ⟨s3,tailCalls,tailRun,tailChain,tailRequests⟩
  have finalIndex : 1 + (N - 1) = N := by omega
  rw [finalIndex,Bytes.fill_word] at tailRun
  have one : ((1 : Nat) : Int) = 1 := by decide
  simp only [one] at tailRun
  have post3 : PostRegs s3.regs := by rw [tailChain.registers,regs]; exact post.post
  rcases MemM1.MemReadDBE.be_false s3 post3.el0 post3.nrw post3.noRME post3.vhe
      post3.aa64el0 post3.ns post3.e2h post3.tge post3.e0e with ⟨s4,endian,endFrame⟩
  have chain := Loops.readChain_append firstChain
    (Loops.readChain_prepend choiceFrame tailChain)
  have completed := Loops.readChain_append chain (ReadChain.nil endFrame)
  simp only [List.append_nil] at completed
  refine ⟨s4,firstCalls ++ tailCalls,aligned,?_,completed,?_⟩
  · have stop : (Sail.Int.toNatChecked (N -i 1) : Int) = (1 : Int) + ((N - 1 : Nat) : Int) - 1 := by
      have nonneg : 0 ≤ (N : Int) - 1 := by omega
      simp only [Sail.Int.toNatChecked,nonneg,ite_true,Int.toNat_of_nonneg]
      omega
    rw [readSuffix_body]
    simp only [Bind.bind,EStateM.bind,firstBody,choice]
    change (EStateM.bind
      (forIn ({start := 1,stop := (Sail.Int.toNatChecked (N -i 1) : Int),step := 1} : IntRange)
        (Bytes.fill initial target 1)
        (fun i word => do let next ← Loops.readBody a N acc aligned i word; pure (.yield next)))
      (fun word => do
        let be ← BigEndian acc.acctype
        pure (if be then reverse_endianness word else word))) s2 = _
    rw [stop]
    simp only [EStateM.bind]
    rw [tailRun]
    simp only [Bind.bind,EStateM.bind,hA.gpr,endian,Pure.pure,EStateM.pure,Bool.false_eq_true,ite_false]
  · rw [List.map_append,firstRequests,tailRequests]
    rfl

#print axioms readSuffix_run
theorem readPlan_run {N : Nat} (positive : 0 < N) (small : N ≤ 16)
    (offsetBase : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (target : BitVec (N * 8)) (hA : AccDR2 acc)
    (domains : Fin N → BitVec 64 → Prop)
    (specs : (j : Fin N) → TopologyImageSpec (fun q => domains j q.va))
    (configs : Fin N → AttributeConfig) (rows : Fin N → List PermissionRow)
    (mapping : Fin N → BitVec 64 → Option Nat) (pa : Fin N → BitVec 56)
    (mapped : ∀ j : Fin N, mapping j (BitVec.addInt a (j.val : Int)) = some (pa j).toNat)
    (ram : ∀ j : Fin N, NotMMIO (pa j)) (s : Loops.State)
    (host : HostPins s)
    (disabled : _get_SCTLR_EL2_Type_A (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1)
    (plain : Plain acc)
    (member : ∀ j : Fin N, domains j (BitVec.addInt a (j.val : Int)))
    (data : ∀ j : Fin N, S1AccessData (specs j) (configs j) (rows j)
      (Loops.byteQuery a acc false j.val))
    (current : ∀ j : Fin N, CurrentS1At (specs j) (configs j) (rows j) s)
    (access : ∀ j : Fin N, CurrentS1AccessAt (specs j) (configs j) (rows j) (mapping j)
      (Loops.byteQuery a acc false j.val) (data j) s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs2 s.regs) (dcache : currentDCache s.regs = true)
    (raw : ∀ j : Fin N, RawImageAt (specs j).imageRows s.mem)
    (none : ∀ j : Fin N,
      NoUpdateRows {(specs j).params with haft := hostHAFT s.regs} acc (specs j).imageRows = true)
    (bytes : ∀ j : Fin N, s.mem[(pa j).toNat]? = some (target.extractLsb' (8 * j.val) 8)) :
    ∃ (after : Loops.State) (calls : List ReadCall) (aligned : Bool),
      Logical.read_bytePlan a N acc s = .ok target after ∧ ReadChain s calls after ∧
      calls.map ReadCall.request =
        Loops.byteAccess offsetBase a acc false 0 ::
          (List.range' 1 (N - 1)).map (Loops.byteAccess offsetBase a acc aligned) := by
  rcases readPrefix_run a N acc s host disabled plain with ⟨initial,u,preRun,frame⟩
  rcases readSuffix_run positive small offsetBase a acc initial target hA
      domains specs configs rows mapping pa mapped ram u member data
      (fun j => current_s1_frame (current j) frame.1 frame.2.1)
      (fun j => (access j).of_regs frame.1)
      (by rw [frame.1]; exact mode) (by rw [frame.1]; exact debug)
      (by rw [frame.1]; exact post) (by rw [frame.1]; exact dcache)
      (by intro j; rw [frame.2.1]; exact raw j)
      (by intro j; rw [frame.1]; exact none j)
      (by intro j; rw [frame.2.1]; exact bytes j) with
    ⟨after,calls,aligned,run,chain,requests⟩
  refine ⟨after,calls,aligned,?_,Loops.readChain_prepend frame chain,requests⟩
  rw [readPlan_eq]
  simp only [Bind.bind,EStateM.bind,preRun,run]

#print axioms readPlan_run
theorem read_bytes_low {N : Nat} (hn : N = 8 ∨ N = 16)
    (offsetBase : Nat) (a : BitVec 64) (acc : AccessDescriptor) (pair : Bool)
    (unaligned : Logical.accessAligned a N pair = false)
    (target : BitVec (N * 8)) (hA : AccDR2 acc)
    (domains : Fin N → BitVec 64 → Prop)
    (specs : (j : Fin N) → TopologyImageSpec (fun q => domains j q.va))
    (configs : Fin N → AttributeConfig) (rows : Fin N → List PermissionRow)
    (mapping : Fin N → BitVec 64 → Option Nat) (pa : Fin N → BitVec 56)
    (mapped : ∀ j : Fin N, mapping j (BitVec.addInt a (j.val : Int)) = some (pa j).toNat)
    (ram : ∀ j : Fin N, NotMMIO (pa j)) (s : Loops.State)
    (profile : AccessProfile) (pins : ProfileAt profile s)
    (notJoin : (s.regs.FeatureImpl[111] &&
      (Align_bits (BitVec.subInt (BitVec.addInt a (N : Int)) 1) 16 == Align_bits a 16)) = false)
    (plain : Plain acc)
    (member : ∀ j : Fin N, domains j (BitVec.addInt a (j.val : Int)))
    (data : ∀ j : Fin N, S1AccessData (specs j) (configs j) (rows j)
      (Loops.byteQuery a acc false j.val))
    (current : ∀ j : Fin N, CurrentS1At (specs j) (configs j) (rows j) s)
    (access : ∀ j : Fin N, CurrentS1AccessAt (specs j) (configs j) (rows j) (mapping j)
      (Loops.byteQuery a acc false j.val) (data j) s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs2 s.regs) (dcache : currentDCache s.regs = true)
    (raw : ∀ j : Fin N, RawImageAt (specs j).imageRows s.mem)
    (none : ∀ j : Fin N,
      NoUpdateRows {(specs j).params with haft := hostHAFT s.regs} acc (specs j).imageRows = true)
    (bytes : ∀ j : Fin N, s.mem[(pa j).toNat]? = some (target.extractLsb' (8 * j.val) 8)) :
    ∃ (after : Loops.State) (calls : List ReadCall) (aligned : Bool),
      Mem_read__2 a N acc pair false s = .ok target after ∧ ReadChain s calls after ∧
      calls.map ReadCall.request =
        Loops.byteAccess offsetBase a acc false 0 ::
          (List.range' 1 (N - 1)).map (Loops.byteAccess offsetBase a acc aligned) := by
  have positive : 0 < N := by rcases hn with rfl | rfl <;> omega
  have small : N ≤ 16 := by rcases hn with rfl | rfl <;> omega
  rcases readPlan_run positive small offsetBase a acc target hA domains specs configs rows mapping pa
      mapped ram s pins.host pins.alignment_disabled plain member data current access mode debug post
      dcache raw none bytes with ⟨after,calls,aligned,run,chain,requests⟩
  refine ⟨after,calls,aligned,?_,chain,requests⟩
  rw [Logical.read_bytes_low a N hn pair unaligned acc hA plain s profile pins notJoin]
  exact run

#print axioms read_bytes_low
end NativeAccess.Plans
