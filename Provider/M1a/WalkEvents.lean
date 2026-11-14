import M1a.TranslateWalkPath
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a.WEv
abbrev State := SequentialState Regs oracleChoiceSource

/- Event-tracking walk (item 2; isla Δ_fetch). The actual FetchDescriptor logs
   exactly one Event.memRead of 8 bytes at the descriptor PA (sail_mem_read via PhysMemRead);
   every other step of the walk prefix logs nothing. -/

/-- The event the actual FetchDescriptor appends for a 64-bit descriptor read. -/
def ttwEv (addr : AddressDescriptor) (acc : AccessDescriptor) (ti : TranslationInfo) : Event :=
  Event.memRead addr.paddress.address.toNat 8
    (Option.map (fun x => x.toNat) (read_request acc (some ti) 8 addr.vaddress addr.paddress.address).va)
    (read_request acc (some ti) 8 addr.vaddress addr.paddress.address).access_kind
    (read_request acc (some ti) 8 addr.vaddress addr.paddress.address).tag

/-- A translation-table read: 8 bytes at physical address pa, access kind AK_ttw, tag false
    (isla e7c8 / defects 2316: kind and tag pinned; va is the request's walk VA field). -/
def IsTTWRead (pa : Nat) (e : Event) : Prop :=
  ∃ va, e = Event.memRead pa 8 va (.AK_ttw ()) false

theorem ttwEv_is (addr : AddressDescriptor) (acc : AccessDescriptor) (ti : TranslationInfo)
    (hk : acc.acctype = .AccessType_TTW) :
    IsTTWRead addr.paddress.address.toNat (ttwEv addr acc ti) := by
  exact ⟨some addr.vaddress.toNat, by simp [ttwEv, read_request, AccessDescriptor_to_Access_kind, hk]⟩

/-- The walk's NewAccDesc(TTW) descriptor has acctype TTW (actual native, EL0 or EL1). -/
theorem new_acctype (s : State)
    (hEL : s.regs.PSTATE.EL = 0#2 ∨ s.regs.PSTATE.EL = 1#2)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) :
    ∃ (out : AccessDescriptor) (t : State), NewAccDesc .AccessType_TTW s = .ok out t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events ∧
      out.acctype = .AccessType_TTW := by
  rcases S1AccDescFrame.new_total s hEL hNoRME hA64 hEL3A64 hNoEL3A32 with
    ⟨out, t, hr, hrg, hm, he⟩
  refine ⟨out, t, hr, hrg, hm, he, ?_⟩
  rw [S2AccDesc.new_eq s hNoRME hA64 hEL3A64 hNoEL3A32] at hr
  have key : ∀ r : EStateM.Result (Sail.Error exception) State AccessDescriptor,
      r = S2AccDesc.new_native s →
      (match r with | .ok o _ => o.acctype = .AccessType_TTW | .error _ _ => True) := by
    intro r hr'
    subst hr'
    rcases hEL with h | h <;> observe_simp [S2AccDesc.new_native]
  have := key _ rfl
  rw [hr] at this
  exact this

theorem fetch_events (ee : BitVec 1) (fault : FaultRecord) (data : BitVec 64)
    (acc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo) (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hTableRAM : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (hold : S2ByteMemory.DescAt s.mem addr.paddress.address.toNat data) :
    ∃ t, FetchDescriptor ee addr acc fault 64 ti s = .ok (fault, S2FetchFrame.decoded ee data) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events.push (ttwEv addr acc ti) := by
  rw [S2FetchFrame.from_descriptor ee fault data acc addr ti s hNoRME hTableRAM hold]
  delta S2Fetch.native
  run_tac Lean.Elab.Tactic.liftMetaTactic fun g => g.withContext do
    let t ← g.getType
    let t ← Lean.Meta.transform t (pre := fun e => do
      if e.isAppOf ``Nat.div.go || e.isAppOf ``Sail.Int.toNatChecked then
        return .done (← Lean.Meta.withTransparency .all <| Lean.Meta.whnf e)
      return .continue)
    return [← g.change t]
  simp [S2FetchFrame.decoded, ttwEv]

#print axioms fetch_events
#print axioms new_acctype
/-- S1OuterPrefix.total (walk package) with events, for a non-EL1&0 regime (EL2&0: no stage 2,
    so the descriptor read is the direct FetchDescriptor): the prefix appends exactly one
    8-byte TTW read at the descriptor PA. -/
theorem prefix_events (wp : S1TTWParams) (va : BitVec 64) (regime : Regime)
    (acc : AccessDescriptor) (startlevel : Int)
    (aligned : Bool) (descaddr : FullAddress) (d : BitVec 64) (typ : DescriptorType)
    (fault : FaultRecord) (a64 s2fs1mro : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (current : TTWState) (data : BitVec 64) (s : State)
    (hReg : (regime == .Regime_EL10) = false)
    (hFault : fault.statuscode = .Fault_None)
    (hEL : s.regs.PSTATE.EL = 0#2 ∨ s.regs.PSTATE.EL = 1#2)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hRAM : S2TableRAM.OrdinaryRAM descaddr.address)
    (hOld : S2ByteMemory.DescAt s.mem descaddr.address.toNat data) :
    ∃ (out : S1OuterPrefix.Input) (t : State),
      S1OuterPrefix.action wp va regime acc startlevel
        (aligned, descaddr, d, typ, fault, a64, s2fs1mro, skl, walkaddr, current) s =
        .ok (.ok out) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧
      out.descriptor = S2FetchFrame.decoded wp.ee data ∧
      out.fault = {fault with level := current.level} ∧
      out.walkaddr = {walkaddr with paddress := descaddr} ∧
      ∃ e, IsTTWRead descaddr.address.toNat e ∧ t.events = s.events.push e := by
  rcases new_acctype s hEL hNoRME hA64 hEL3A64 hNoEL3A32 with ⟨base, t1, hnew, hr1, hm1, he1, hk⟩
  have hacc : CreateAccDescS1TTW (current.level == startlevel) (AArch64_GetVARange va) acc s =
      .ok (S1ReadAccDesc.value (current.level == startlevel) (AArch64_GetVARange va) acc base) t1 := by
    simp [CreateAccDescS1TTW, S1ReadAccDesc.value, Bind.bind, Pure.pure, EStateM.bind,
      EStateM.pure, hnew]
  let k1 := t1.choiceOcc.getD 1603 0
  let u1 : State := {t1 with choiceOcc := t1.choiceOcc.insert 1603 (k1 + 1)}
  have hl1 : occLabel 1603 t1 = .ok (.occ 1603 k1) u1 := rfl
  rcases S1UnknownFault.total (.occ 1603 k1) u1 with ⟨s2fault, t2, hf, hr2, hm2, he2⟩
  let k2 := t2.choiceOcc.getD 1604 0
  let u2 : State := {t2 with choiceOcc := t2.choiceOcc.insert 1604 (k2 + 1)}
  have hl2 : occLabel 1604 t2 = .ok (.occ 1604 k2) u2 := rfl
  rcases S1Unknowns.undefined_address_total (.occ 1604 k2) u2 with
    ⟨unused, t3, hu, hr3, hm3, he3⟩
  have hRegs3 : t3.regs = s.regs := hr3.trans (hr2.trans hr1)
  have hMem3 : t3.mem = s.mem := hm3.trans (hm2.trans hm1)
  have hEv3 : t3.events = s.events := he3.trans (he2.trans he1)
  rcases fetch_events wp.ee {fault with level := current.level} data (S1ReadAccDesc.value (current.level == startlevel) (AArch64_GetVARange va) acc base)
    {walkaddr with paddress := descaddr} ({regime := regime, vmid := none, asid := none, va := walkaddr.vaddress, s1level := some current.level, s2info := none, s1params := some wp, s2params := none, memattrs := walkaddr.memattrs} : TranslationInfo) t3 (by rw [hRegs3]; exact hNoRME) hRAM
    (by rw [hMem3]; exact hOld) with ⟨t5, hfd, hr5, hm5, he5⟩
  have hread : S1DescriptorRead.action false aligned a64 s2fs1mro wp.ee
      {fault with level := current.level} s2fault {walkaddr with paddress := descaddr}
      current.level (S1ReadAccDesc.value (current.level == startlevel) (AArch64_GetVARange va) acc base)
      ({regime := regime, vmid := none, asid := none, va := walkaddr.vaddress, s1level := some current.level, s2info := none, s1params := some wp, s2params := none, memattrs := walkaddr.memattrs} : TranslationInfo) t3 =
      .ok (.ok (aligned, S2FetchFrame.decoded wp.ee data, {fault with level := current.level},
        a64, s2fault, s2fs1mro)) t5 := by
    simp [S1DescriptorRead.action, Bind.bind, Pure.pure, Functor.map, ExceptT.bind,
      ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift, EStateM.bind, EStateM.map,
      EStateM.pure, liftM, MonadLiftT.monadLift, MonadLift.monadLift, hfd]
  let k3 := t5.choiceOcc.getD 1605 0
  let t6 : State := {t5 with choiceOcc := t5.choiceOcc.insert 1605 (k3 + 1)}
  have hl3 : occLabel 1605 t5 = .ok (.occ 1605 k3) t6 := rfl
  rcases S1Unknowns.bits_at_total 64 (.occ 1605 k3) t6 with ⟨newd, hb⟩
  have hNoFault : ((.Fault_None : Fault) != .Fault_None) = false := by decide
  have hel2 : (if regime == .Regime_EL10 then EL2Enabled () else pure false : SailM Bool) t3 =
      .ok false t3 := by simp only [hReg, Bool.false_eq_true, ↓reduceIte]; rfl
  refine ⟨⟨aligned, S2FetchFrame.decoded wp.ee data, {fault with level := current.level},
    a64, s2fault, s2fs1mro, newd, {walkaddr with paddress := descaddr}⟩, t6, ?_,
    hr5.trans hRegs3, hm5.trans hMem3, rfl, rfl, rfl,
    ⟨ttwEv {walkaddr with paddress := descaddr} (S1ReadAccDesc.value (current.level == startlevel) (AArch64_GetVARange va) acc base)
      ({regime := regime, vmid := none, asid := none, va := walkaddr.vaddress, s1level := some current.level, s2info := none, s1params := some wp, s2params := none, memattrs := walkaddr.memattrs} : TranslationInfo),
      ttwEv_is _ _ _ hk, ?_⟩⟩
  · simp only [hReg, Bool.false_eq_true, ↓reduceIte] at hel2 ⊢
    simp [S1OuterPrefix.action, hReg, Bind.bind, Pure.pure, Functor.map, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.mk, ExceptT.lift, ExceptT.map, EStateM.bind, EStateM.map, EStateM.pure,
      liftM, MonadLiftT.monadLift, MonadLift.monadLift, hacc, hl1, hf, hl2, hu,
      hread, hl3, hb]
    simp [hFault, hNoFault, Sail.Int.toNatChecked, Sail.BitVec.castWidth, Bind.bind, Pure.pure, Functor.map, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.mk, ExceptT.lift, ExceptT.map, EStateM.bind, EStateM.map, EStateM.pure,
      liftM, MonadLiftT.monadLift, MonadLift.monadLift, hl3, hb]
  · show t5.events = s.events.push _
    rw [he5, hEv3]

#print axioms prefix_events
open S1OuterSetup S1LogicalReference ArmCert.Eval.M1a in
/-- The actual EL2&0 table step (next state, entry address, OA range check) logs no events. -/
theorem next_events (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams) (d : BitVec 64)
    (s : State) :
    match S1NextTable.native current s2fs1mro wp d s with
    | .ok _ t => t.events = s.events
    | .error _ _ => True := by
  observe_simp [S1NextTable.native]

theorem cert_events (wp : S1TTWParams) (current : TTWState) (d va : BitVec 64)
    (s2fs1mro : Bool) (s : State)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hLevel : 0 ≤ current.level ∧ current.level ≤ 2)
    (hPA : s.regs.bank_Int .__supported_pa_size = 48)
    (c : S1TablePrefix.Certificate wp current d va s2fs1mro s) : c.state.events = s.events := by
  have h1 := next_events current s2fs1mro wp d s
  have hf := S1NextTableFacts.native_frame current s2fs1mro wp d s
  rw [← S1NextTable.complete current s2fs1mro wp d s hD128 hDS hTG, c.next_eq] at h1 hf
  dsimp only at h1
  simp only [S1NextTableFacts.frame] at hf
  have hl : 0 ≤ c.next.level ∧ c.next.level ≤ 3 := by rw [c.level_eq]; omega
  rcases S1EntryFrame.total c.next.level 0#2 wp.txsz va c.next.baseaddress c.afterNext hl with
    ⟨u, hu, hfu⟩
  have h2 := c.address_eq
  rw [hu] at h2
  simp only [EStateM.Result.ok.injEq] at h2
  have hu' : u = c.afterAddress := h2.2
  subst hu'
  have hpa : c.afterAddress.regs.bank_Int .__supported_pa_size = 48 := by rw [hfu.1, hf.1]; exact hPA
  rcases S2OAFrame.total (S1TablePrefix.address c.next va).address wp.ps c.afterAddress hpa with
    ⟨v, hv, _, _, hev⟩
  have h3 := c.range_eq
  rw [hv] at h3
  simp only [EStateM.Result.ok.injEq] at h3
  rw [← h3.2, hev, hfu.2.2, h1]

theorem outer_table20_ev (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor) (startlevel : Int)
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
      next.permissions.uxn_table = current.permissions.uxn_table ∧
      ∃ e, IsTTWRead descaddr.address.toNat e ∧ t.events = s.events.push e := by
  rcases prefix_events wp va .Regime_EL20 acc startlevel aligned descaddr d typ fault a64
    s2fs1mro skl walkaddr current data s (by decide) hFault hEL hNoRME hA64
    hEL3A64 hNoEL3A32 hRAM hOld with ⟨r, t1, hp, hr1, hm1, hd, hf, ha, e, he, hev1⟩
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
  have hce := cert_events wp current r.descriptor va r.s2fs1mro t1 hD128 hDS hTG hl
    (by rw [hr1]; exact hPA) c
  rcases ArmCert.Eval.M1a.table20_exact wp va acc r.walkaddr (S1OuterSplit.info wp .Regime_EL20 current r.walkaddr)
    r.s2fs1mro r.aligned descaddr r.descriptor typ r.fault r.newd r.a64 r.s2fault skl current t1
    hD128 hDS hTG hHaft hTable' c hRange' with ⟨hl1, hr2, hm2⟩
  have hperm := ArmCert.Eval.M1a.perm_certificate wp current r.descriptor va r.s2fs1mro t1 hD128 hDS hTG
    (by rw [hd]; exact hz) c
  refine ⟨r, c.next, c.state, ?_, hr2.trans hr1, hm2.trans hm1, c.level_eq,
    S1NextTable20PAS.certificate_pas wp current r.descriptor va r.s2fs1mro t1 hD128 hDS hTG hPAS c,
    hperm.1, hperm.2, e, he, by rw [hce, hev1]⟩
  have hres : S1OuterSplit.resume wp va .Regime_EL20 acc descaddr typ skl current r t1 =
      .ok (.ok (r.aligned, S1TablePrefix.address c.next va, r.descriptor, .DescriptorType_Table,
        r.fault, r.a64, r.s2fs1mro, 0#2, r.walkaddr, c.next)) c.state := by
    simp [S1OuterSplit.resume, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
      ExceptT.pure, Pure.pure, EStateM.bind, EStateM.pure, hl1]
  rw [hslot, ← hd] at hres
  rw [S1OuterSplit.equation, ← hd, ← hf, ← ha]
  simp [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, Pure.pure,
    EStateM.bind, EStateM.pure, hp, hres]


open ArmCert.Eval.M1a in
theorem outer_leaf_ev (regime : Regime) (hRegime : S1LeafBoth.Regimes regime)
    (hReg10 : (regime == .Regime_EL10) = false)
    (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor) (startlevel : Int)
    (aligned : Bool) (descaddr : FullAddress) (d : BitVec 64) (typ : DescriptorType)
    (fault : FaultRecord) (a64 s2fs1mro : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (current : TTWState) (cfg : S2Interface.Config)
    (data : BitVec 64) (s : State)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hAIE : wp.aie = 0#1) (hMAIR : wp.mair = 0x000000040044ffff#64)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure)
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
    (hLeaf : S1DecodeFacts.classify (S2FetchFrame.decoded wp.ee data) current.level =
      .DescriptorType_Leaf) :
    ∃ (r : S1OuterPrefix.Input) (next : TTWState) (t : State),
      S1WalkSource.named.body0 wp va regime acc 64 startlevel
        (aligned, descaddr, d, typ, fault, a64, s2fs1mro, skl, walkaddr, current) s =
        .ok (.ok (r.aligned, descaddr, S2FetchFrame.decoded wp.ee data, .DescriptorType_Leaf,
          {fault with level := current.level}, r.a64, r.s2fs1mro, skl,
          {walkaddr with paddress := descaddr}, next)) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧
      S1LeafShape.Shape wp current (S2FetchFrame.decoded wp.ee data) next ∧
      LeafValue regime current r.s2fs1mro wp (S2FetchFrame.decoded wp.ee data) next s.regs ∧
      ∃ e, IsTTWRead descaddr.address.toNat e ∧ t.events = s.events.push e := by
  rcases prefix_events wp va regime acc startlevel aligned descaddr d typ fault a64
    s2fs1mro skl walkaddr current data s hReg10 hFault hEL hNoRME hA64
    hEL3A64 hNoEL3A32 hRAM hOld with ⟨r, t1, hp, hr1, hm1, hd, hf, ha, e, he, hev1⟩
  have hLeaf' : S1DecodeFacts.classify r.descriptor current.level = .DescriptorType_Leaf := by
    rw [hd]; exact hLeaf
  rcases ArmCert.Eval.M1a.leaf_loop regime hRegime wp va acc r.walkaddr
    (S1OuterSplit.info wp regime current r.walkaddr) r.s2fs1mro r.aligned descaddr
    r.descriptor typ r.fault r.newd r.a64 r.s2fault skl current t1
    hD128 hDS hTG hAIE hMAIR hSS hPAS hLeaf' with ⟨next, t, hl, hr2, hm2, he2, hs, hv⟩
  refine ⟨r, next, t, ?_, hr2.trans hr1, hm2.trans hm1, by rw [← hd]; exact hs, ?_, e, he,
    by rw [he2, hev1]⟩
  · rw [S1OuterSplit.equation]
    have hres : S1OuterSplit.resume wp va regime acc descaddr typ skl current r t1 =
        .ok (.ok (r.aligned, descaddr, r.descriptor, .DescriptorType_Leaf, r.fault, r.a64,
          r.s2fs1mro, skl, r.walkaddr, next)) t := by
      simp [S1OuterSplit.resume, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
        ExceptT.pure, Pure.pure, EStateM.bind, EStateM.pure, hl]
    rw [← hd, ← hf, ← ha]
    simp [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, Pure.pure,
      EStateM.bind, EStateM.pure, hp, hres]
  · rw [← hd, ← hr1]; exact hv


#print axioms next_events
#print axioms cert_events
#print axioms outer_table20_ev
#print axioms outer_leaf_ev
open S1OuterSetup ArmCert.Eval.M1a

/-- The TTW reads of a Walk20 path, in walk order: one 8-byte read at each visited slot. -/
inductive ReadsAlong (wp : S1TTWParams) (va : BitVec 64) (mem : S1ResourcePath.Memory) :
    Nat → Int → FullAddress → Array Event → Prop where
  | leaf {level slot e} (h : IsTTWRead slot.address.toNat e) : ReadsAlong wp va mem 1 level slot #[e]
  | table {n level slot data e W}
      (desc : S2ByteMemory.DescAt mem slot.address.toNat data)
      (h : IsTTWRead slot.address.toNat e)
      (rest : ReadsAlong wp va mem n (level + 1)
        (S1ResourcePath.nextSlot va level (S2FetchFrame.decoded wp.ee data)) W) :
      ReadsAlong wp va mem (n + 1) level slot (#[e] ++ W)

theorem ReadsAlong.size {wp : S1TTWParams} {va : BitVec 64} {mem : S1ResourcePath.Memory}
    {n : Nat} {level : Int} {slot : FullAddress} {W : Array Event}
    (h : ReadsAlong wp va mem n level slot W) : W.size = n := by
  induction h with
  | leaf _ => rfl
  | table _ _ _ ih => simp [ih]; omega

theorem trace20_ev (c : Context) (hEL20 : c.regime = .Regime_EL20) (hHaft : c.wp.haft = 0#1)
    {n : Nat} {level : Int} {slot : FullAddress} {L : Int} {S : FullAddress} {D : BitVec 64}
    {mem : S1ResourcePath.Memory}
    (h : Walk20 c.wp c.va mem n level slot L S D) :
    ∀ (s : State), Ready c s → s.mem = mem → ∀ (aligned : Bool) (d : BitVec 64) (typ : DescriptorType) (fault : FaultRecord)
      (a64 mro : Bool) (skl : BitVec 2) (walkaddr : AddressDescriptor) (current : TTWState),
      current.level = level → fault.statuscode = .Fault_None →
      current.baseaddress.paspace = .PAS_NonSecure →
      current.permissions.ap_table = 0#2 → current.permissions.uxn_table = 0#1 →
      ∃ (y : Vars) (t : State),
        S2Loop.Trace stop (S1WalkSource.named.body0 c.wp c.va c.regime c.acc 64 c.startlevel)
          n (aligned, slot, d, typ, fault, a64, mro, skl, walkaddr, current) s (.ok y) t ∧
        t.regs = s.regs ∧ t.mem = s.mem ∧ LeafEnd c.wp s.regs L S D y ∧
        ∃ W, t.events = s.events ++ W ∧ ReadsAlong c.wp c.va mem n level slot W := by
  induction h with
  | @leaf lv sl data bounds ram desc hleaf =>
    intro s hReady hsm aligned d typ fault a64 mro skl walkaddr current hlv hf hpas hap hux
    rw [← hsm] at desc
    subst hlv
    rw [hEL20]
    rcases outer_leaf_ev .Regime_EL20 (Or.inr rfl) (by decide) c.wp c.va c.acc c.startlevel aligned sl d typ
      fault a64 mro skl walkaddr current c.cfg data s c.d128 c.ds c.tg c.aie c.mair hpas hf
      hReady.config c.vm c.dc c.ss hReady.el hReady.noRME hReady.a64 hReady.el3A64
      hReady.noEL3A32 ram desc hleaf with ⟨r, next, t, hrun, hr, hm, hs, hv, e, he, hev⟩
    refine ⟨_, t, .done hrun rfl, hr, hm, ⟨rfl, rfl, rfl, by simp [hf], rfl,
      current, rfl, hpas, hap, hux, hs, hv⟩, #[e], by rw [hev]; rfl, .leaf he⟩
  | @table m lv sl data L' S' D' bounds ram desc htable range hperm rest ih =>
    intro s hReady hsm aligned d typ fault a64 mro skl walkaddr current hlv hf hpas hap hux
    rw [← hsm] at desc
    subst hlv
    rcases outer_table20_ev c.wp c.va c.acc c.startlevel aligned sl d typ fault a64 mro skl walkaddr
      current c.cfg data s c.d128 c.ds c.tg hHaft bounds hpas hReady.pa hf
      hReady.config c.vm c.dc c.ss hReady.el hReady.noRME hReady.a64 hReady.el3A64
      hReady.noEL3A32 ram desc htable range hperm with
      ⟨r, next, t1, hrun, hr1, hm1, hnl, hnp, hna, hnu, e, he, hev1⟩
    have hReady1 : Ready c t1 := hReady.of_regs hr1
    rcases ih t1 hReady1 (hm1.trans hsm) r.aligned (S2FetchFrame.decoded c.wp.ee data) .DescriptorType_Table
      {fault with level := current.level} r.a64 r.s2fs1mro 0#2 {walkaddr with paddress := sl} next
      hnl (by simpa using hf) hnp (hna.trans hap) (hnu.trans hux) with
      ⟨y, u, htrace, hr2, hm2, hend, W, hW, hR⟩
    refine ⟨y, u, ?_, hr2.trans hr1, hm2.trans hm1, by rw [← hr1]; exact hend, #[e] ++ W,
      by rw [hW, hev1, Array.push_eq_append, Array.append_assoc], .table (by rw [← hsm]; exact desc) he hR⟩
    rw [hEL20] at htrace ⊢
    exact .next hrun rfl htrace


#print axioms trace20_ev
theorem suffix_ev (wp : S1TTWParams) (va : BitVec 64) (regime : Regime)
    (acc : AccessDescriptor) (ctx : TLBContext) (entry : TLBRecord)
    (aligned : Bool) (slot : FullAddress) (d : BitVec 64) (f : FaultRecord)
    (a64 mro : Bool) (skl : BitVec 2) (walkaddr : AddressDescriptor) (w : TTWState)
    (s : State)
    (hd : wp.d128 = 0#1) (htg : wp.tgx = .TGx_4KB)
    (hl : w.level = 3) (hc : w.contiguous = 0#1)
    (hpas : w.baseaddress.paspace = .PAS_NonSecure)
    (hf : f.statuscode = .Fault_None)
    (hAF : BitVec.join1 [BitVec.access d 10] = 1#1)
    (hOA : (!is_zero_subrange (S1StageOA.address va w).address 55
      (S2PhysicalSizeFrame.value wp.ps)) = false)
    (hPA : s.regs.bank_Int .__supported_pa_size = 48)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false) :
    ∃ t : State,
      S1WalkSuffixSource.suffix wp va regime acc 64 ctx entry
        (aligned, slot, d, .DescriptorType_Leaf, f, a64, mro, skl, walkaddr, w) s =
        .ok (.ok (f, walkaddr, w, d)) t ∧ t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rcases S1StageOA.total va w s (by omega) with ⟨t1, hoa, hf1⟩
  rcases S2OAFrame.total (S1StageOA.address va w).address wp.ps t1 (by rw [hf1.1]; exact hPA) with
    ⟨t2, hrange, hr2, hm2, he2⟩
  have hc2 : t2.regs.bank_Bool .__tlb_enabled = false := by rw [hr2, hf1.1]; exact hCache
  have hguard := S1CacheGuard.disabled d f t2 hc2
  have hamec := ArmCert.Eval.M1a.amec_eq wp .PAS_NonSecure regime d hd t1
  have hAF0 : ¬ (BitVec.join1 [BitVec.access d 10] = 0#1) := by rw [hAF]; simp
  have hR : (PASpace.PAS_NonSecure == PASpace.PAS_Realm) = false := by decide
  have hFin : ¬ ((3 : Int) < FINAL_LEVEL) := by decide
  have hNo : ((Fault.Fault_None : Fault) != Fault.Fault_None) = false := by decide
  refine ⟨t2, ?_, hr2.trans hf1.1, hm2.trans hf1.2.1, he2.trans hf1.2.2⟩
  unfold S1WalkSuffixSource.suffix
  simp only [hd, htg, hl, hc]
  simp [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, ExceptT.lift,
    Pure.pure, EStateM.bind, EStateM.pure, EStateM.map, Functor.map, liftM,
    MonadLiftT.monadLift, MonadLift.monadLift, hoa, hrange, hOA, hguard, hf, hAF0,
    hamec, S1WalkChecks.amec, hpas, hR, hFin, hNo, hd, ArmFull.assert, PreSail.assert]


theorem tail_ev (c : Context) (hEL20 : c.regime = .Regime_EL20) (hHaft : c.wp.haft = 0#1)
    (ctx : TLBContext) (entry : TLBRecord) (aligned : Bool) (descaddr : FullAddress)
    (d : BitVec 64) (typ : DescriptorType) (f : FaultRecord) (a64 mro : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (w : TTWState) (s : State) {n : Nat} {L : Int}
    {S : FullAddress} {D : BitVec 64}
    (hReady : Ready c s) (hFault : f.statuscode = .Fault_None)
    (hPAS : w.baseaddress.paspace = .PAS_NonSecure)
    (hap : w.permissions.ap_table = 0#2) (hux : w.permissions.uxn_table = 0#1)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false)
    (hWalk : Walk20 c.wp c.va s.mem n w.level descaddr L S D)
    (hL3 : L = 3)
    (hContig : S1Contiguous.bit (S2FetchFrame.decoded c.wp.ee D) = 0#1)
    (hAF : BitVec.join1 [BitVec.access (S2FetchFrame.decoded c.wp.ee D) 10] = 1#1)
    (hOA : ∀ v : TTWState, v.level = 3 →
      v.baseaddress.address = S1LeafBaseFrame.base (S2FetchFrame.decoded c.wp.ee D) 3 →
      (!is_zero_subrange (S1StageOA.address c.va v).address 55
        (S2PhysicalSizeFrame.value c.wp.ps)) = false) :
    ∃ (fr : FaultRecord) (wa : AddressDescriptor) (next : TTWState) (t : State),
      S1WalkTail.action c ctx entry aligned descaddr d typ f a64 mro skl walkaddr w s =
        .ok (fr, wa, next, S2FetchFrame.decoded c.wp.ee D) t ∧
      fr.statuscode = .Fault_None ∧ fr.level = 3 ∧
      (∃ (cur : TTWState) (m : Bool), cur.level = 3 ∧
        cur.baseaddress.paspace = .PAS_NonSecure ∧
        cur.permissions.ap_table = 0#2 ∧ cur.permissions.uxn_table = 0#1 ∧
        S1LeafShape.Shape c.wp cur (S2FetchFrame.decoded c.wp.ee D) next ∧
        LeafValue .Regime_EL20 cur m c.wp (S2FetchFrame.decoded c.wp.ee D) next s.regs) ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧
      ∃ W, t.events = s.events ++ W ∧ ReadsAlong c.wp c.va s.mem n w.level descaddr W := by
  rcases trace20_ev c hEL20 hHaft hWalk s hReady rfl aligned d typ f a64 mro skl walkaddr w rfl
    hFault hPAS hap hux with ⟨y, t, htrace, hr, hm, hend, W, hW, hRA⟩
  have hlen := ArmCert.Eval.M1a.walk20_length hWalk
  have hloop : S1WalkSource.named.loop0 c.wp c.va c.regime c.acc 64 a64 aligned f w c.startlevel
      d skl walkaddr mro typ descaddr s = .ok (.ok y) t := by
    simpa only [S1WalkSource.named.loop0, stop] using
      S2Loop.execute htrace 1048576 (by omega)
  rcases y with ⟨aligned', slot', d', typ', f', a64', mro', skl', walkaddr', next⟩
  rcases hend with ⟨hslot, hd', htyp, hfs, hfl, cur, hcl, hcp, hca, hcu, hshape, hval⟩
  subst hd' htyp
  rcases hshape with ⟨hist, hlev, hbase, hnpas, hcontig, _⟩
  have hnl : next.level = 3 := by rw [hlev, hcl, hL3]
  have hnc : next.contiguous = 0#1 := by
    rw [hcontig, hContig]; split <;> rfl
  rcases suffix_ev c.wp c.va c.regime c.acc ctx entry aligned' slot'
    (S2FetchFrame.decoded c.wp.ee D) f' a64' mro' skl' walkaddr' next t c.d128 c.tg hnl hnc hnpas
    hfs hAF (hOA next hnl (by rw [hbase, hcl, hL3]))
    (by rw [hr]; exact hReady.pa) (by rw [hr]; exact hCache) with ⟨u, hsuf, hr2, hm2, he2⟩
  refine ⟨f', walkaddr', next, u, ?_, hfs, by rw [hfl, hL3], ⟨cur, mro', by rw [hcl, hL3], hcp,
    hca, hcu, ⟨hist, hlev, hbase, hnpas, hcontig, by assumption⟩, hval⟩, hr2.trans hr, hm2.trans hm,
    W, by rw [he2, hW], hRA⟩
  simp [S1WalkTail.action, S1WalkTailSource.tail, SailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, Bind.bind, ExceptT.bind, ExceptT.mk,
    ExceptT.run, ExceptT.bindCont, EStateM.bind, Pure.pure, EStateM.pure, hloop, hsuf]


#print axioms suffix_ev
#print axioms tail_ev
open S1EntryWP S1Normality in
theorem walk_result_ev (c : Context) (f : FaultRecord) (s : State) (n : Nat) {L : Int}
    {S : FullAddress} {D : BitVec 64}
    (hEL20 : c.regime = .Regime_EL20) (hHaft : c.wp.haft = 0#1)
    (hvr : AArch64_GetVARange c.va = .VARange_LOWER)
    (hEPD0 : _get_TCR_EL2_Type_EPD0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1)
    (hReady : Ready c s) (hFault : f.statuscode = .Fault_None)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false)
    (hTx : c.wp.txsz = 16#6) (hStart : c.startlevel = 0)
    (hRootIn : (!is_zero_subrange (S1EntryRoot.slot c.wp s.regs c.regime c.va).address
      55 (S2PhysicalSizeFrame.value c.wp.ps)) = false)
    (hWalk : Walk20 c.wp c.va s.mem n 0 (S1EntryRoot.slot c.wp s.regs c.regime c.va) L S D)
    (hL3 : L = 3)
    (hContig : S1Contiguous.bit (S2FetchFrame.decoded c.wp.ee D) = 0#1)
    (hAF : BitVec.join1 [BitVec.access (S2FetchFrame.decoded c.wp.ee D) 10] = 1#1)
    (hOA : ∀ v : TTWState, v.level = 3 →
      v.baseaddress.address = S1LeafBaseFrame.base (S2FetchFrame.decoded c.wp.ee D) 3 →
      (!is_zero_subrange (S1StageOA.address c.va v).address 55
        (S2PhysicalSizeFrame.value c.wp.ps)) = false) :
    ∃ r t, AArch64_S1Walk f c.wp c.va c.regime c.acc 64 s = .ok r t ∧
      (PostR c s D r t ∧ ∃ W, t.events = s.events ++ W ∧ ReadsAlong c.wp c.va s.mem n 0 (S1EntryRoot.slot c.wp s.regs c.regime c.va) W) := by
  rw [S1WalkSource.named.equation, S1WalkTailSource.equation]
  unfold S1WalkTailSource.withTail
  apply run_wp
  apply bind_normal_me _ _ s _ _ (S1EntryDraws.bool_draw 1591)
  intro a64 t1 hf1
  apply bind_normal_me _ _ t1 _ _ (S1EntryDraws.bool_draw 1592)
  intro aligned t2 hf2
  apply bind_normal_me _ _ t2 _ _ (S1EntryDraws.context_draw 1593)
  intro ctx t3 hf3
  apply bind_normal_me _ _ t3 _ _ (S1EntryDraws.record_draw 1594)
  intro entry t4 hf4
  have hf14 := frame_trans (frame_trans (frame_trans hf1 hf2) hf3) hf4
  have hc : t4.regs.bank_Bool .__tlb_enabled = false := by rw [hf14.1]; exact hCache
  have hread : (readReg ArmFull.Register.__tlb_enabled : SailM Bool) t4 = .ok false t4 := by
    change EStateM.Result.ok (t4.regs.bank_Bool .__tlb_enabled) t4 = .ok false t4
    rw [hc]
  apply bind_lift_eq _ _ t4 t4 false _ _ hread
  simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  have hup : HasUnprivileged c.regime = true := by
    rcases c.regimes with h | h <;> rw [h] <;> rfl
  simp only [hup, ↓reduceIte]
  apply bind_wp
  refine ⟨.ok false, t4, ?_, ?_⟩
  · have he := ArmCert.Eval.M1a.epd20_eq c.va hvr t4
    have hE : _get_TCR_EL2_Type_EPD0 (t4.regs.bank_BitVec_64 .TCR_EL2) = 0#1 := by
      rw [hf14.1]; exact hEPD0
    rw [hEL20]
    simp [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.lift, Pure.pure,
      ExceptT.pure, EStateM.bind, EStateM.pure, EStateM.map, Functor.map, liftM,
      MonadLiftT.monadLift, MonadLift.monadLift, he, hE]
  simp only [S1EntryWP.Post]
  rw [c.ss]
  rcases S1EntryRoot.total c.wp c.va c.regime t4 c.regimes c.d128 c.ds c.tg hTx
    (by rw [hf14.1]; exact hReady.el3A64) (by rw [hf14.1]; exact hReady.noEL3A32) with
    ⟨w, t6, hinit, hf6, hs, hb⟩
  apply bind_lift_eq _ _ t4 t6 w _ _ hinit
  have hf16 := frame_trans hf14 hf6
  apply bind_normal_me _ _ t6 _ _ (S1EntryDraws.bits_draw 1595)
  intro d t7 hf7
  have hf17 := frame_trans hf16 hf7
  apply bind_normal_me _ _ t7 _ _ (S1EntryDraws.address_draw 1596)
  intro initialAddress t8 hf8
  have hf18 := frame_trans hf17 hf8
  have hmec : AArch64_TTWalkMECID c.wp.emec c.regime .SS_NonSecure t8 =
      .ok DEFAULT_MECID t8 := by rw [S1EntryCallees.mecid_eq]; rfl
  apply bind_lift_eq _ _ t8 t8 DEFAULT_MECID _ _ hmec
  apply bind_lift_normal _ _ t8 _ _ (S1EntryCallees.dcache_normal c.regime c.regimes)
  intro enabled t9 hf9
  have hf19 := frame_trans hf18 hf9
  apply bind_normal_me _ _ t9 _ _
  · apply S1NormalME.normal_ite
    · intro hdisabled
      apply S1NormalME.normal_bind
      · exact S1NormalME.lift_normal _ _ S1EntryCalleesExtra.normalnc_normal
      · intro attrs
        exact S1NormalME.normal_pure _ _
    · intro henabled
      exact S1NormalME.normal_pure _ _
  · intro walkaddr t10 hf10
    have hf110 := frame_trans hf19 hf10
    have hv : _get_HCR_EL2_Type_VM (t10.regs.bank_BitVec_64 .HCR_EL2) = 0#1 := by
      rw [hf110.1, hReady.config.hHCR]
      exact c.vm
    apply S1EntryShare.bind_disabled c.regime _ t10 _ _ hv
    intro t11 hf11
    have hf111 := frame_trans hf110 hf11
    apply bind_normal_me _ _ t11 _ _ (S1EntryDraws.type_draw 1597)
    intro typ t12 hf12
    have hf112 := frame_trans hf111 hf12
    have hp := hs.2.2.1
    have hb0 : w.baseaddress.address = S1EntryRoot.base c.wp s.regs c.regime c.va := by
      rw [hf14.1] at hb
      exact hb
    have hbase : w.baseaddress =
        {address := S1EntryRoot.base c.wp s.regs c.regime c.va, paspace := .PAS_NonSecure} := by
      cases he : w.baseaddress with
      | mk pas addr =>
        simp only [he] at hp hb0
        simp only [he, hp, hb0]
    rcases S1InitialEntryAddress.total c.wp c.va w.baseaddress t12 c.d128 c.tg hTx with
      ⟨t13, ha, hf13⟩
    have ha0 : AArch64_S1SLTTEntryAddress w.level c.wp c.va w.baseaddress t12 =
        .ok (S1EntryRoot.slot c.wp s.regs c.regime c.va) t13 := by
      simpa only [hs.1, hbase, S1EntryRoot.slot] using ha
    apply bind_lift_eq _ _ t12 t13 (S1EntryRoot.slot c.wp s.regs c.regime c.va) _ _ ha0
    have hf113 := frame_trans hf112 hf13
    rcases S2OAFrame.total (S1EntryRoot.slot c.wp s.regs c.regime c.va).address c.wp.ps t13
      (by rw [hf113.1]; exact hReady.pa) with ⟨t14, hrange, hr14, hm14, he14⟩
    have hrange0 : AArch64_OAOutOfRange
        (S1EntryRoot.slot c.wp s.regs c.regime c.va).address c.wp.d128 c.wp.ps c.wp.tgx t13 =
        .ok (!is_zero_subrange (S1EntryRoot.slot c.wp s.regs c.regime c.va).address
          55 (S2PhysicalSizeFrame.value c.wp.ps)) t14 := by
      simpa only [c.d128, c.tg] using hrange
    apply bind_lift_eq _ _ t13 t14 _ _ _ hrange0
    have hf114 := frame_trans hf113 ⟨hr14, hm14, he14⟩
    have hout : (!is_zero_subrange (S1EntryRoot.slot c.wp s.regs c.regime c.va).address
        55 (S2PhysicalSizeFrame.value c.wp.ps)) = false := hRootIn
    rw [hout]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hc14 : t14.regs.bank_Bool .__tlb_enabled = false := by
      rw [hf114.1]; exact hCache
    have hwalk14 : Walk20 c.wp c.va t14.mem n w.level
        (S1EntryRoot.slot c.wp s.regs c.regime c.va) L S D := by
      rw [hf114.2.1, hs.1]; exact hWalk
    rcases tail_ev c hEL20 hHaft ctx entry aligned (S1EntryRoot.slot c.wp s.regs c.regime c.va)
      d typ f a64 false 0#2
      {walkaddr with memattrs := {walkaddr.memattrs with
        shareability := EffectiveShareability walkaddr.memattrs}, tlbcontext := ctx}
      w t14 (hReady.of_regs hf114.1) hFault hp hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1
      hc14 hwalk14 hL3 hContig hAF hOA with
      ⟨fr, wa, next, u, hrun, h1, h2, h3, hr, hm, W, hW, hRA⟩
    have posteq : (fun r v => PostR c t14 D r v ∧ ∃ W, v.events = t14.events ++ W ∧
        ReadsAlong c.wp c.va t14.mem n w.level (S1EntryRoot.slot c.wp s.regs c.regime c.va) W) =
        (fun r v => PostR c s D r v ∧ ∃ W, v.events = s.events ++ W ∧
        ReadsAlong c.wp c.va s.mem n 0 (S1EntryRoot.slot c.wp s.regs c.regime c.va) W) := by
      funext r v
      simp only [PostR, Res, hf114.1, hf114.2.1, hf114.2.2, hs.1, hStart]
    rw [← posteq]
    simpa only [hStart, hs.1] using
      (S1EntryWP.of_run _ t14 u (fr, wa, next, S2FetchFrame.decoded c.wp.ee D)
        (fun r v => PostR c t14 D r v ∧ ∃ W, v.events = t14.events ++ W ∧
          ReadsAlong c.wp c.va t14.mem n w.level (S1EntryRoot.slot c.wp s.regs c.regime c.va) W)
        hrun ⟨⟨hr, hm, rfl, h1, h2, h3⟩, W, hW, hRA⟩)



#print axioms walk_result_ev
open S1LogicalReference

theorem walk20_count {wp : S1TTWParams} {va : BitVec 64} {mem : S1ResourcePath.Memory}
    {n : Nat} {level : Int} {slot : FullAddress} {L : Int} {S : FullAddress} {D : BitVec 64}
    (h : Walk20 wp va mem n level slot L S D) : (n : Int) = L - level + 1 := by
  induction h with
  | leaf => simp
  | table _ _ _ _ _ _ _ ih => push_cast; omega

theorem walk_result_path_ev (c : Context) (f : FaultRecord) (s : State)
    (hEL20 : c.regime = .Regime_EL20) (hHaft : c.wp.haft = 0#1)
    (hvr : AArch64_GetVARange c.va = .VARange_LOWER)
    (hEPD0 : _get_TCR_EL2_Type_EPD0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1)
    (hReady : Ready c s) (hFault : f.statuscode = .Fault_None)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false)
    (hTx : c.wp.txsz = 16#6) (hStart : c.startlevel = 0)
    (hRootIn : (!is_zero_subrange (S1EntryRoot.slot c.wp s.regs c.regime c.va).address
      55 (S2PhysicalSizeFrame.value c.wp.ps)) = false)
    (observe : Observation)
    (available : Available observe (fun p => S2TableRAM.OrdinaryRAM p.address))
    (realizes : Realizes observe (c.wp.ee == 1#1) (c.wp.pie == 1#1)
      (c.wp.ha == 1#1) (c.wp.hd == 1#1) (fun a => s.mem[a]?))
    (identity : S1EntryPathSlots.Identity observe)
    (htab : ∀ l p v d, observe l p v → BytesAt (c.wp.ee == 1#1) (fun a => s.mem[a]?) p d →
      ∀ level : Nat, descriptorKind level v.stable = .ok .table → TablePermsZero d)
    (slotL : Nat) (physL : FullAddress) (vL : S1DescriptorPIE.View 64)
    (path : Path observe (S2PhysicalSizeFrame.value c.wp.ps).toNat c.va 0 9
      ((S1EntryRoot.base c.wp s.regs c.regime c.va).setWidth 48) (.leaf 3 slotL physL vL))
    (hleaf : ∀ d, BytesAt (c.wp.ee == 1#1) (fun a => s.mem[a]?) physL d →
      S1Contiguous.bit d = 0#1 ∧ BitVec.join1 [BitVec.access d 10] = 1#1 ∧
      ∀ v : TTWState, v.level = 3 → v.baseaddress.address = S1LeafBaseFrame.base d 3 →
        (!is_zero_subrange (S1StageOA.address c.va v).address 55
          (S2PhysicalSizeFrame.value c.wp.ps)) = false) :
    ∃ (D : BitVec 64) (r : FaultRecord × AddressDescriptor × TTWState × BitVec 64) (t : State),
      BytesAt (c.wp.ee == 1#1) (fun a => s.mem[a]?) physL (S2FetchFrame.decoded c.wp.ee D) ∧
      AArch64_S1Walk f c.wp c.va c.regime c.acc 64 s = .ok r t ∧ PostR c s D r t ∧
      ∃ W, t.events = s.events ++ W ∧ W.size = 4 ∧ ReadsAlong c.wp c.va s.mem 4 0 (S1EntryRoot.slot c.wp s.regs c.regime c.va) W := by
  have hroot := S1EntryRootGeometry.root_slot c.wp s.regs c.regime c.va c.d128 c.tg hTx
  rcases ArmCert.Eval.M1a.of_path20 c.wp c.va s.mem observe available realizes identity htab path
    slotL physL vL rfl rfl (S1EntryRoot.slot c.wp s.regs c.regime c.va) hroot with
    ⟨n, S, D, hw, _, hbytes⟩
  rcases hleaf _ hbytes with ⟨hc, haf, hoa⟩
  have hn : n = 4 := by have := walk20_count hw; omega
  subst hn
  rcases walk_result_ev c f s 4 hEL20 hHaft hvr hEPD0 hReady hFault hCache hTx hStart hRootIn
    hw rfl hc haf hoa with ⟨r, t, hr, hp, W, hW, hRA⟩
  exact ⟨D, r, t, hbytes, hr, hp, W, hW, hRA.size, hRA⟩


open ArmCert.Eval.M1a.TWP ArmCert.Eval.JointSAT

/-- memory's WalkFact plus the walk's exact event delta: the actual S1Walk appends exactly
    four 8-byte TTW reads, one per level, at the slots of the Walk20 path from the root slot. -/
def WalkFactE (s : State) (va : BitVec 64) (D : BitVec 64) : Prop :=
  ∀ t : State, t.regs = s.regs → t.mem = s.mem →
    ∀ (f : FaultRecord) (acc' : AccessDescriptor), f.statuscode = .Fault_None →
      acc'.ss = .SS_NonSecure →
      ∃ (wp : S1TTWParams) (u : State),
        AArch64_GetS1TTWParams .Regime_EL20 acc'.ss va t = .ok wp u ∧
        S1Normality.Frame t u ∧ EL20.Fields.Fields wp ∧ EL20.Active wp ∧
        ∀ v : State, v.regs = t.regs → v.mem = t.mem →
          ∃ (c : Context) (r : FaultRecord × AddressDescriptor × TTWState × BitVec 64)
            (w : State), c.wp = wp ∧ c.acc = acc' ∧ c.va = va ∧ c.regime = .Regime_EL20 ∧
            AArch64_S1Walk f wp va .Regime_EL20 acc' 64 v = .ok r w ∧ PostR c v D r w ∧
            ∃ W, w.events = v.events ++ W ∧ W.size = 4 ∧
              ReadsAlong wp va v.mem 4 0 (rootSlot s.regs va) W

theorem WalkFactE.walkFact {s : State} {va D : BitVec 64} (h : WalkFactE s va D) :
    WalkFact s va D := by
  intro t htr htm f acc' hf hss
  rcases h t htr htm f acc' hf hss with ⟨wp, u, hg, hfr, hF, hA, hv⟩
  refine ⟨wp, u, hg, hfr, hF, hA, fun v hvr hvm => ?_⟩
  rcases hv v hvr hvm with ⟨c, r, w, a, b, d, e, hw, hp, _⟩
  exact ⟨c, r, w, a, b, d, e, hw, hp⟩



#print axioms ReadsAlong.size
#print axioms WalkFactE.walkFact
#print axioms walk20_count
#print axioms walk_result_path_ev
end ArmCert.Eval.M1a.WEv
