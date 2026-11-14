import MemM1.MemWriteD6
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.MemWriteD7
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3
open MemM1.MemWriteD4 MemM1.MemWriteD5 MemM1.MemWriteD6
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2

theorem akT (acc : AccessDescriptor) (hA : AccDWT acc) : AccessDescriptor_to_Access_kind acc = akPlain :=
  ak_gpr acc hA.base.gpr hA.exclusive hA.atomicop hA.acqpc hA.acqsc hA.relsc

/-- The strengthened data-translation premise hE' (as the read side's readD_strong): on any state
    with `s`'s registers and memory, TranslateAddress at `a` succeeds to PA `pa` (NS, Normal),
    returns `vaddress = a`, and keeps registers and memory. -/
def StrongTA (a : BitVec 64) (acc : AccessDescriptor) (n : Nat) (pa : BitVec 56) (s : State) : Prop :=
  ∀ u : State, u.regs = s.regs → u.mem = s.mem → ∃ ad t1,
    AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
    ad.fault.statuscode = .Fault_None ∧
    ad.paddress = { paspace := .PAS_NonSecure, address := pa } ∧
    ad.memattrs.memtype = .MemType_Normal ∧ ad.vaddress = a ∧
    t1.regs = u.regs ∧ t1.mem = u.mem

/-- **Mem_set (STRB n = 1, STR/STP-half n = 8, ...) under the strengthened premise.** Registers
    unchanged, memory = `s.mem` with the `n` bytes written little-endian at `pa`, and the event log
    = TranslateAddress's (from a framed `u`) followed by exactly
    `memWrite pa n (some a) (AK_explicit plain/normal) (some v) none`.
    `tagchecked` is free: TagOK (in PreW) closes MTE. -/
theorem memset_strongT (a : BitVec 64) (n : Nat) (hn : SizeOK n) (ha : a.toNat % n = 0)
    (acc : AccessDescriptor) (s : State) (v : BitVec (n * 8)) (hA : AccDWT acc) (pa : BitVec 56)
    (hP : PreW acc s.regs) (hspe : s.regs.bank_Bool .SPESampleInFlight = false)
    (hE' : StrongTA a acc n pa s) (hio : NotMMIO pa) :
    ∃ u ad t1 t, Frame s u ∧ AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      Mem_set a n acc v s = .ok () t ∧
      t.events = t1.events.push (.memWrite pa.toNat n (some a.toNat) akPlain
        (some (Sail.BitVec.castWidth (m := 8 * n) v)) none) ∧
      t.regs = s.regs ∧ t.mem = wfold s.mem pa.toNat n (wbyte v) ∧
      (∀ p, t.mem[p]? = if pa.toNat ≤ p ∧ p < pa.toNat + n
        then some (wbyte v (p - pa.toNat)) else s.mem[p]?) := by
  let Q : AddressDescriptor → State → Prop := fun ad t1 => ∃ u, Frame s u ∧
    AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧ ad.vaddress = a ∧
    t1.regs = s.regs ∧ t1.mem = s.mem
  have hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ TagOK acc t1.regs ∧ Q ad t1 := by
    intro u fu
    rcases hE' u fu.1 fu.2.1 with ⟨ad, t1, h, hf, hpa, hmt, hv, hr, hm⟩
    have hr' : t1.regs = s.regs := hr.trans fu.1
    refine ⟨ad, t1, h, hf, by rw [hpa], by rw [hr']; exact hspe, by unfold TagOK; rw [hr']; exact hP.tag,
      u, fu, h, hv, hr', hm.trans fu.2.1⟩
  rcases memset_skelT a n hn ha acc s pa v hA hP.tag Q hTA hio (littleEndian_of acc s hA hP) with
    ⟨ad, t1, t, ⟨u, fu, h, hv, hr, hm⟩, hset, hev, hreg, hmem⟩
  refine ⟨u, ad, t1, t, fu, h, hset, by rw [hev, akT acc hA, hv], hreg.trans hr, by rw [hmem, hm], ?_⟩
  intro p
  rw [hmem, wfold_get, hm]

/-- **STRB post-index (crypto: Mem_set a 1 acc v, tagchecked = TRUE) under the strengthened
    premise.** MTE closed by FEAT_MTE2 absent (FeatureImpl[134] = false, part of PreW.tag). -/
theorem strb_strong (a : BitVec 64) (acc : AccessDescriptor) (s : State) (v : BitVec (1 * 8))
    (hA : AccDWT acc) (pa : BitVec 56)
    (hP : PreW acc s.regs) (hspe : s.regs.bank_Bool .SPESampleInFlight = false)
    (hE' : StrongTA a acc 1 pa s) (hio : NotMMIO pa) :
    ∃ u ad t1 t, Frame s u ∧ AArch64_TranslateAddress a acc true ((1 : Nat) : Int) u = .ok ad t1 ∧
      Mem_set a 1 acc v s = .ok () t ∧
      t.events = t1.events.push (.memWrite pa.toNat 1 (some a.toNat) akPlain
        (some (Sail.BitVec.castWidth (m := 8 * 1) v)) none) ∧
      t.regs = s.regs ∧ t.mem = wfold s.mem pa.toNat 1 (wbyte v) ∧
      (∀ p, t.mem[p]? = if pa.toNat ≤ p ∧ p < pa.toNat + 1
        then some (wbyte v (p - pa.toNat)) else s.mem[p]?) :=
  memset_strongT a 1 (Or.inl rfl) (Nat.mod_one _) acc s v hA pa hP hspe hE' hio

/-- **STP 64-bit, FEAT_LSE2 implemented (crypto: Mem_set__1 a 16 acc true (data2 ++ data1)) under
    the strengthened premise + Normal inner/outer Write-Back attributes.** ONE 16-byte write. -/
theorem stp_lse2_strong (a : BitVec 64) (ha : a.toNat % 16 = 0)
    (acc : AccessDescriptor) (s : State) (v : BitVec (16 * 8)) (hA : AccDWT acc) (pa : BitVec 56)
    (hP : PreW acc s.regs) (hspe : s.regs.bank_Bool .SPESampleInFlight = false)
    (hLSE : s.regs.FeatureImpl[111] = true)
    (hE' : ∀ u : State, u.regs = s.regs → u.mem = s.mem → ∃ ad t1,
      AArch64_TranslateAddress a acc true ((16 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = { paspace := .PAS_NonSecure, address := pa } ∧
      ad.memattrs.memtype = .MemType_Normal ∧
      ad.memattrs.inner.attrs = MemAttr_WB ∧ ad.memattrs.outer.attrs = MemAttr_WB ∧
      ad.vaddress = a ∧ t1.regs = u.regs ∧ t1.mem = u.mem)
    (hio : NotMMIO pa) :
    ∃ u ad t1 t, Frame s u ∧ AArch64_TranslateAddress a acc true ((16 : Nat) : Int) u = .ok ad t1 ∧
      Mem_set__1 a 16 acc true v s = .ok () t ∧
      t.events = t1.events.push (.memWrite pa.toNat 16 (some a.toNat) akPlain
        (some (Sail.BitVec.castWidth (m := 8 * 16) v)) none) ∧
      t.regs = s.regs ∧ t.mem = wfold s.mem pa.toNat 16 (wbyte v) ∧
      (∀ p, t.mem[p]? = if pa.toNat ≤ p ∧ p < pa.toNat + 16
        then some (wbyte v (p - pa.toNat)) else s.mem[p]?) := by
  let Q : AddressDescriptor → State → Prop := fun ad t1 => ∃ u, Frame s u ∧
    AArch64_TranslateAddress a acc true ((16 : Nat) : Int) u = .ok ad t1 ∧ ad.vaddress = a ∧
    t1.regs = s.regs ∧ t1.mem = s.mem
  have hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true ((16 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ TagOK acc t1.regs ∧ Q ad t1 := by
    intro u fu
    rcases hE' u fu.1 fu.2.1 with ⟨ad, t1, h, hf, hpa, hmt, hin, hout, hv, hr, hm⟩
    have hr' : t1.regs = s.regs := hr.trans fu.1
    refine ⟨ad, t1, h, hf, by rw [hpa], hmt, hin, hout, by rw [hr']; exact hspe,
      by unfold TagOK; rw [hr']; exact hP.tag, u, fu, h, hv, hr', hm.trans fu.2.1⟩
  rcases memset1_pair_skel a ha acc s pa v hA hP.tag hLSE Q hTA hio (littleEndian_of acc s hA hP) with
    ⟨ad, t1, t, ⟨u, fu, h, hv, hr, hm⟩, hset, hev, hreg, hmem⟩
  refine ⟨u, ad, t1, t, fu, h, hset, by rw [hev, akT acc hA, hv], hreg.trans hr, by rw [hmem, hm], ?_⟩
  intro p
  rw [hmem, wfold_get, hm]

/-- **STP 64-bit, FEAT_LSE2 absent (crypto: Mem_set a 8 acc data1; Mem_set (a+8) 8 acc data2)
    under the strengthened premise.** The second TranslateAddress runs on the state after the
    first write, so its premise is stated on states with `s`'s registers and the memory after the
    first write (`wfold s.mem pa1 8 (wbyte d1)`); this is what a walk-based proof gives when the
    written bytes are not table bytes. Two translations, two 8-byte writes, in order. -/
theorem stp_nolse2_strong (a b : BitVec 64) (ha : a.toNat % 8 = 0) (hb : b.toNat % 8 = 0)
    (acc : AccessDescriptor) (s : State) (d1 d2 : BitVec (8 * 8)) (hA : AccDWT acc)
    (pa1 pa2 : BitVec 56)
    (hP : PreW acc s.regs) (hspe : s.regs.bank_Bool .SPESampleInFlight = false)
    (hE1 : StrongTA a acc 8 pa1 s)
    (hE2 : ∀ s1 : State, s1.regs = s.regs → s1.mem = wfold s.mem pa1.toNat 8 (wbyte d1) →
      StrongTA b acc 8 pa2 s1)
    (hio1 : NotMMIO pa1) (hio2 : NotMMIO pa2) :
    ∃ u1 ad1 t1 s1 u2 ad2 t2 t,
      Frame s u1 ∧ AArch64_TranslateAddress a acc true ((8 : Nat) : Int) u1 = .ok ad1 t1 ∧
      Mem_set a 8 acc d1 s = .ok () s1 ∧
      s1.events = t1.events.push (.memWrite pa1.toNat 8 (some a.toNat) akPlain
        (some (Sail.BitVec.castWidth (m := 8 * 8) d1)) none) ∧
      s1.regs = s.regs ∧ s1.mem = wfold s.mem pa1.toNat 8 (wbyte d1) ∧
      Frame s1 u2 ∧ AArch64_TranslateAddress b acc true ((8 : Nat) : Int) u2 = .ok ad2 t2 ∧
      (do Mem_set a 8 acc d1; Mem_set b 8 acc d2 : SailM Unit) s = .ok () t ∧
      t.events = t2.events.push (.memWrite pa2.toNat 8 (some b.toNat) akPlain
        (some (Sail.BitVec.castWidth (m := 8 * 8) d2)) none) ∧
      t.regs = s.regs ∧
      t.mem = wfold (wfold s.mem pa1.toNat 8 (wbyte d1)) pa2.toNat 8 (wbyte d2) := by
  have h8 : SizeOK 8 := by unfold SizeOK; omega
  rcases memset_strongT a 8 h8 ha acc s d1 hA pa1 hP hspe hE1 hio1 with
    ⟨u1, ad1, t1, s1, fu1, h1, hset1, hev1, hr1, hm1, -⟩
  have hP1 : PreW acc s1.regs := by rw [hr1]; exact hP
  have hspe1 : s1.regs.bank_Bool .SPESampleInFlight = false := by rw [hr1]; exact hspe
  rcases memset_strongT b 8 h8 hb acc s1 d2 hA pa2 hP1 hspe1 (hE2 s1 hr1 hm1) hio2 with
    ⟨u2, ad2, t2, t, fu2, h2, hset2, hev2, hr2, hm2, -⟩
  refine ⟨u1, ad1, t1, s1, u2, ad2, t2, t, fu1, h1, hset1, hev1, hr1, hm1, fu2, h2, ?_, hev2,
    hr2.trans hr1, by rw [hm2, hm1]⟩
  simp only [Bind.bind, EStateM.bind, hset1, hset2]

/-- **Mem_set under abstract E17 (tagchecked free).** E17 plus the post-translation register facts
    `PostW` (SPESampleInFlight = false, TagOK) on TranslateAddress's result state, which E17's
    ProjRegsEq does not give; `PreW` on `s` (BigEndian inputs + TagOK, read BEFORE translation, so
    E17 is not involved). The event's va field is `ad.vaddress` (E17 does not fix it). -/
theorem memset_E17T (m : ConsumerMap) (a : BitVec 64) (n : Nat) (hn : SizeOK n) (ha : a.toNat % n = 0)
    (acc : AccessDescriptor) (s : State) (v : BitVec (n * 8)) (hA : AccDWT acc)
    (hE : ∀ u : State, u.regs = s.regs → u.mem = s.mem → TranslationAgrees m u)
    (hp : m.permitted a acc true (n : Int)) (hio : NotMMIO (m.pa a)) (hP : PreW acc s.regs)
    (hPost : ∀ u ad t1, Frame s u → AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 →
      PostW acc t1.regs) :
    ∃ u ad t1 t, Frame s u ∧ AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = { paspace := .PAS_NonSecure, address := m.pa a } ∧
      ad.memattrs.memtype = .MemType_Normal ∧
      Mem_set a n acc v s = .ok () t ∧
      t.events = t1.events.push (.memWrite (m.pa a).toNat n (some ad.vaddress.toNat) akPlain
        (some (Sail.BitVec.castWidth (m := 8 * n) v)) none) ∧
      ProjRegsEq s.regs t.regs ∧
      (∀ p, ¬ m.tableByte p → t.mem[p]? = if (m.pa a).toNat ≤ p ∧ p < (m.pa a).toNat + n
        then some (wbyte v (p - (m.pa a).toNat)) else s.mem[p]?) := by
  let Q : AddressDescriptor → State → Prop := fun ad t1 => ∃ u, Frame s u ∧
    AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
    ad.fault.statuscode = .Fault_None ∧
    ad.paddress = { paspace := .PAS_NonSecure, address := m.pa a } ∧
    ad.memattrs.memtype = .MemType_Normal ∧ ProjRegsEq s.regs t1.regs ∧
    ∀ p, ¬ m.tableByte p → t1.mem[p]? = s.mem[p]?
  have hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = m.pa a ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ TagOK acc t1.regs ∧ Q ad t1 := by
    intro u fu
    rcases hE u fu.1 fu.2.1 a acc true (n : Int) hp with ⟨ad, t1, h, hf, hpa, hmt, hr, hm⟩
    rw [fu.1] at hr
    have hq := hPost u ad t1 fu h
    refine ⟨ad, t1, h, hf, by rw [hpa], hq.spe, hq.tag, u, fu, h, hf, hpa, hmt, hr, ?_⟩
    intro p hp'
    rw [hm p hp', fu.2.1]
  rcases memset_skelT a n hn ha acc s (m.pa a) v hA hP.tag Q hTA hio (littleEndian_of acc s hA hP) with
    ⟨ad, t1, t, ⟨u, fu, h, hf, hpa, hmt, hr, hm⟩, hset, hev, hreg, hmem⟩
  refine ⟨u, ad, t1, t, fu, h, hf, hpa, hmt, hset, by rw [hev, akT acc hA], by rw [hreg]; exact hr, ?_⟩
  intro p hp'
  rw [hmem, wfold_get]
  split
  · rfl
  · exact hm p hp'

/-- `memset_E17T` gives `UnmappedSame m s t` under `MapOK m`. -/
theorem memset_E17T_unmapped (m : ConsumerMap) (hM : MapOK m) (a : BitVec 64) (n : Nat) (hn : SizeOK n)
    (ha : a.toNat % n = 0) (acc : AccessDescriptor) (s : State) (v : BitVec (n * 8)) (hA : AccDWT acc)
    (hE : ∀ u : State, u.regs = s.regs → u.mem = s.mem → TranslationAgrees m u)
    (hp : m.permitted a acc true (n : Int)) (hio : NotMMIO (m.pa a)) (hP : PreW acc s.regs)
    (hPost : ∀ u ad t1, Frame s u → AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 →
      PostW acc t1.regs) :
    ∃ t, Mem_set a n acc v s = .ok () t ∧ ProjRegsEq s.regs t.regs ∧ UnmappedSame m s t := by
  rcases memset_E17T m a n hn ha acc s v hA hE hp hio hP hPost with
    ⟨u, ad, t1, t, fu, h, hf, hpa, hmt, hset, hev, hr, hget⟩
  exact ⟨t, hset, hr, unmapped_of m hM a acc n hp s t _ hget⟩

#print axioms memset_strongT
#print axioms strb_strong
#print axioms stp_lse2_strong
#print axioms stp_nolse2_strong
#print axioms memset_E17T
#print axioms memset_E17T_unmapped
end MemM1.MemWriteD7
