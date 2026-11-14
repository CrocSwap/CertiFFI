import M1a.PermBase
import Walk.S1ResourcePath
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a

/-- EL2&0 table step with hardware AF-on-table updates off (wp.haft = 0): the
    descriptor is not rewritten and memory is EXACTLY unchanged. -/
theorem table20_exact (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo) (s2fs1mro aligned : Bool)
    (descaddr : FullAddress) (d : BitVec 64) (oldType : DescriptorType)
    (fault : FaultRecord) (oldNew : BitVec 64) (a64 : Bool) (s2fault : FaultRecord)
    (skl : BitVec 2) (current : TTWState) (s : State)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hHaft : wp.haft = 0#1)
    (hTable : S1DecodeFacts.classify d current.level = .DescriptorType_Table)
    (c : S1TablePrefix.Certificate wp current d va s2fs1mro s)
    (hRange : S1TablePrefix.outOfRange wp (S1TablePrefix.address c.next va) = false) :
    S1WalkSource.named.loop1 wp va .Regime_EL20 acc 64 descaddr oldType skl current
        walkaddr ti aligned d fault a64 s2fault s2fs1mro oldNew s =
      .ok (.ok (aligned, S1TablePrefix.address c.next va, d,
        .DescriptorType_Table, fault, d, a64, s2fault, 0#2, c.next)) c.state ∧
    c.state.regs = s.regs ∧ c.state.mem = s.mem := by
  have hSame : S1TableUpdate.word wp d = d := by
    simp [S1TableUpdate.word, hHaft]
  have ha : S1WalkTable.action wp va acc walkaddr ti s2fs1mro aligned d fault a64 s2fault
      current s = .ok (.ok (aligned, S1TablePrefix.address c.next va, d,
        .DescriptorType_Table, fault, d, a64, s2fault, 0#2, c.next)) c.state := by
    have h := hSame
    rw [S1TableUpdate.word_def] at h
    simp [S1WalkTable.action, h, Bind.bind, Pure.pure, Functor.map,
      ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift,
      EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift,
      MonadLift.monadLift, c.next_eq, c.address_eq, c.range_eq, hRange]
  have hr : S1WalkSource.named.body1 wp va .Regime_EL20 acc 64 walkaddr ti s2fs1mro
      (aligned, descaddr, d, oldType, fault, oldNew, a64, s2fault, skl, current) s =
      .ok (.ok (aligned, S1TablePrefix.address c.next va, d,
        .DescriptorType_Table, fault, d, a64, s2fault, 0#2, c.next)) c.state := by
    rw [S1WalkTable.equation wp va acc walkaddr ti s2fs1mro aligned descaddr d oldType
      fault oldNew a64 s2fault skl current s hD128 hDS hTG hTable]
    exact ha
  have trace : S2Loop.Trace S1WalkInvalid.stop
      (S1WalkSource.named.body1 wp va .Regime_EL20 acc 64 walkaddr ti s2fs1mro)
      1 (aligned, descaddr, d, oldType, fault, oldNew, a64, s2fault, skl, current) s
      (.ok (aligned, S1TablePrefix.address c.next va, d,
        .DescriptorType_Table, fault, d, a64, s2fault, 0#2, c.next)) c.state :=
    .done hr (by simp [S1WalkInvalid.stop])
  refine ⟨?_, c.regs_eq, c.mem_eq⟩
  simpa only [S1WalkSource.named.loop1, S1WalkInvalid.stop] using
    S2Loop.execute trace 1048576 (by decide)

#print axioms table20_exact
end ArmCert.Eval.M1a

namespace ArmCert.Eval.M1a

/-- Outer EL2&0 walk step at an in-range table slot, haft = 0: exact next vars,
    registers and memory unchanged. -/
theorem outer_table20 (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor) (startlevel : Int)
    (aligned : Bool) (descaddr : FullAddress) (d : BitVec 64) (typ : DescriptorType)
    (fault : FaultRecord) (a64 s2fs1mro : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (current : TTWState) (cfg : S2Interface.Config)
    (data : BitVec 64) (s : State)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hHaft : wp.haft = 0#1)
    (hLevel : 0 ≤ current.level ∧ current.level ≤ 3)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure)
    (hPA : s.regs.bank_Int .__supported_pa_size = 48)
    (hFault : fault.statuscode = .Fault_None)
    (hConfig : S2Interface.ConfigAt cfg s)
    (hVM : _get_HCR_EL2_Type_VM cfg.hcr = 0#1)
    (hDC : _get_HCR_EL2_Type_DC cfg.hcr = 0#1)
    (hSS : acc.ss = .SS_NonSecure)
    (hEL : s.regs.PSTATE.EL = 0#2 ∨ s.regs.PSTATE.EL = 1#2)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hRAM : S2TableRAM.OrdinaryRAM descaddr.address)
    (hOld : S2ByteMemory.DescAt s.mem descaddr.address.toNat data)
    (hTable : S1DecodeFacts.classify (S2FetchFrame.decoded wp.ee data) current.level =
      .DescriptorType_Table)
    (hRange : S1TablePrefix10.outOfRange wp
      (S1ResourcePath.nextSlot va current.level (S2FetchFrame.decoded wp.ee data)) = false)
    (hz : TablePermsZero (S2FetchFrame.decoded wp.ee data)) :
    ∃ (r : S1OuterPrefix.Input) (next : TTWState) (t : State),
      S1WalkSource.named.body0 wp va .Regime_EL20 acc 64 startlevel
        (aligned, descaddr, d, typ, fault, a64, s2fs1mro, skl, walkaddr, current) s =
        .ok (.ok (r.aligned,
          S1ResourcePath.nextSlot va current.level (S2FetchFrame.decoded wp.ee data),
          S2FetchFrame.decoded wp.ee data, .DescriptorType_Table,
          {fault with level := current.level}, r.a64, r.s2fs1mro, 0#2,
          {walkaddr with paddress := descaddr}, next)) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧
      next.level = current.level + 1 ∧ next.baseaddress.paspace = .PAS_NonSecure ∧
      next.permissions.ap_table = current.permissions.ap_table ∧
      next.permissions.uxn_table = current.permissions.uxn_table := by
  rcases S1OuterPrefix.total wp va .Regime_EL20 acc startlevel aligned descaddr d typ fault a64
    s2fs1mro skl walkaddr current cfg data s hFault hConfig hVM hDC hSS hEL hNoRME hA64
    hEL3A64 hNoEL3A32 hRAM hOld with ⟨r, t1, hp, hr1, hm1, hd, hf, ha⟩
  have hTable' : S1DecodeFacts.classify r.descriptor current.level = .DescriptorType_Table := by
    rw [hd]; exact hTable
  have hl : 0 ≤ current.level ∧ current.level ≤ 2 := by
    have := S1DecodeFacts.table_before_final r.descriptor current.level hLevel.2 hTable'
    omega
  rcases S1TablePrefix.total wp current r.descriptor va r.s2fs1mro t1 hD128 hDS hTG hl
    (by rw [hr1]; exact hPA) with ⟨c⟩
  have hshape := S1NextTable20Shape.certificate_shape wp current r.descriptor va r.s2fs1mro t1
    hD128 hDS hTG hPAS c
  have hslot : S1TablePrefix.address c.next va =
      S1ResourcePath.nextSlot va current.level (S2FetchFrame.decoded wp.ee data) := by
    rw [← hd]; exact S1ResourcePath.next_of_shape va r.descriptor current c.next hshape
  have hRange' : S1TablePrefix.outOfRange wp (S1TablePrefix.address c.next va) = false := by
    rw [hslot]; exact hRange
  rcases table20_exact wp va acc r.walkaddr (S1OuterSplit.info wp .Regime_EL20 current r.walkaddr)
    r.s2fs1mro r.aligned descaddr r.descriptor typ r.fault r.newd r.a64 r.s2fault skl current t1
    hD128 hDS hTG hHaft hTable' c hRange' with ⟨hl1, hr2, hm2⟩
  have hperm := perm_certificate wp current r.descriptor va r.s2fs1mro t1 hD128 hDS hTG
    (by rw [hd]; exact hz) c
  refine ⟨r, c.next, c.state, ?_, hr2.trans hr1, hm2.trans hm1, c.level_eq,
    S1NextTable20PAS.certificate_pas wp current r.descriptor va r.s2fs1mro t1 hD128 hDS hTG hPAS c,
    hperm.1, hperm.2⟩
  have hres : S1OuterSplit.resume wp va .Regime_EL20 acc descaddr typ skl current r t1 =
      .ok (.ok (r.aligned, S1TablePrefix.address c.next va, r.descriptor, .DescriptorType_Table,
        r.fault, r.a64, r.s2fs1mro, 0#2, r.walkaddr, c.next)) c.state := by
    simp [S1OuterSplit.resume, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
      ExceptT.pure, Pure.pure, EStateM.bind, EStateM.pure, hl1]
  rw [hslot, ← hd] at hres
  rw [S1OuterSplit.equation, ← hd, ← hf, ← ha]
  simp [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, Pure.pure,
    EStateM.bind, EStateM.pure, hp, hres]

#print axioms outer_table20
end ArmCert.Eval.M1a
