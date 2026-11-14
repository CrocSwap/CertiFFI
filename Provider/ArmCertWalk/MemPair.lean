-- Memory classes: the 16-byte pair access `Mem_read__1/Mem_set__1 A 16 acc true` at
-- ANY 8-aligned VA (caller buffers are not 16-aligned in general): LSE2 single 16-byte access when
-- 16-aligned, else two 8-byte halves each with its own translation (SDK MemPair8R/W skeletons),
-- all from the canonical invariant + decision-171 no-update route; the second store half's
-- translation runs on the post-first-write state (CurrentS1At / RawImageAt carried by separation).
import ArmCertWalk.MemPairCore
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
namespace ArmCertWalk

abbrev plus8 (A : BitVec 64) : BitVec 64 := BitVec.addInt A ((8 : Nat) : Int)

/-- Per-descriptor certificates for the pair's actual access(es) at `A`. -/
def PairAccess {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (A : BitVec 64)
    (acc : AccessDescriptor) (s : State) : Prop :=
  (A.toNat % 16 = 0 → domain ⟨A, ⟨acc, true⟩, ((16 : Nat) : Int)⟩ ∧
    ∃ data : S1AccessData spec config rows ⟨A, ⟨acc, true⟩, ((16 : Nat) : Int)⟩,
      CurrentS1AccessAt spec config rows mapping ⟨A, ⟨acc, true⟩, ((16 : Nat) : Int)⟩ data s) ∧
  (A.toNat % 16 ≠ 0 →
    (domain ⟨A, ⟨acc, true⟩, ((8 : Nat) : Int)⟩ ∧
      ∃ data : S1AccessData spec config rows ⟨A, ⟨acc, true⟩, ((8 : Nat) : Int)⟩,
        CurrentS1AccessAt spec config rows mapping ⟨A, ⟨acc, true⟩, ((8 : Nat) : Int)⟩ data s) ∧
    (domain ⟨plus8 A, ⟨acc, true⟩, ((8 : Nat) : Int)⟩ ∧
      ∃ data : S1AccessData spec config rows ⟨plus8 A, ⟨acc, true⟩, ((8 : Nat) : Int)⟩,
        CurrentS1AccessAt spec config rows mapping ⟨plus8 A, ⟨acc, true⟩, ((8 : Nat) : Int)⟩ data s))

/-- Events of the pair access from `before`: one 16-byte access, or two 8-byte halves. -/
def PairEvents {domain : QueryDomain} (spec : TopologyImageSpec domain) (A : BitVec 64) (pa1 pa2 : BitVec 56)
    (one : Event) (half1 half2 : Event) (before after : Array Event) : Prop :=
  (A.toNat % 16 = 0 ∧ ∃ ad mid, NoUpdateTraffic spec A before ad mid ∧ after = mid.push one) ∨
  (A.toNat % 16 ≠ 0 ∧ ∃ ad1 mid1 ad2 mid2, NoUpdateTraffic spec A before ad1 mid1 ∧
    NoUpdateTraffic spec (plus8 A) (mid1.push half1) ad2 mid2 ∧ after = mid2.push half2)

theorem loadPair_noupdate {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : State) (A : BitVec 64) (h8 : A.toNat % 8 = 0) (acc : AccessDescriptor)
    (hA : MemM1.MemReadD2.AccDR2 acc) (pair : PairAccess spec config rows mapping A acc s)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : MemM1.MemReadD2.PostRegs2 s.regs) (lse2 : s.regs.FeatureImpl[111] = true)
    (dcache : currentDCache s.regs = true)
    (pa1 pa2 : BitVec 56) (mapped1 : mapping A = some pa1.toNat) (mapped2 : mapping (plus8 A) = some pa2.toNat)
    (contiguous : A.toNat % 16 = 0 → pa2.toNat = pa1.toNat + 8)
    (mmio1 : MemM1.MemReadIF.NotMMIO pa1) (mmio2 : MemM1.MemReadIF.NotMMIO pa2)
    (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (value : BitVec (16 * 8))
    (bytes1 : ∀ i < 8, s.mem[pa1.toNat + i]? = some (value.extractLsb' (8 * i) 8))
    (bytes2 : ∀ i < 8, s.mem[pa2.toNat + i]? = some (value.extractLsb' (8 * (i + 8)) 8)) :
    ∃ t, Mem_read__1 A 16 acc true s = .ok value t ∧ t.regs = s.regs ∧ t.mem = s.mem ∧
      PairEvents spec A pa1 pa2
        (.memRead pa1.toNat 16 (some A.toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)
        (.memRead pa1.toNat 8 (some A.toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)
        (.memRead pa2.toNat 8 (some (plus8 A).toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)
        s.events t.events := by
  have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hA.gpr]; rfl
  have kind := MemM1.MemReadD2.kind_eq2 acc hA
  by_cases h16 : A.toNat % 16 = 0
  · obtain ⟨member, data, access⟩ := pair.1 h16
    have bytes : ∀ i < 16, s.mem[pa1.toNat + i]? = some (value.extractLsb' (8 * i) 8) := by
      intro i hi
      by_cases lo : i < 8
      · exact bytes1 i lo
      · have := bytes2 (i - 8) (by omega)
        rw [contiguous h16, show pa1.toNat + 8 + (i - 8) = pa1.toNat + i by omega,
          show i - 8 + 8 = i by omega] at this
        exact this
    obtain ⟨ad, mid, t, call, traffic, _, events, regs, mem⟩ := load16_noupdate spec config rows mapping s A h16
      acc hA member data current access mode debug post lse2 dcache pa1 mapped1 mmio1 raw noUpd value bytes
    exact ⟨t, call, regs, mem, Or.inl ⟨h16, ad, mid, traffic, by rw [events, kind]⟩⟩
  · obtain ⟨⟨member1, data1, access1⟩, ⟨member2, data2, access2⟩⟩ := pair.2 h16
    have tas1 := tas_of_current spec config rows mapping s A acc member1 data1 current access1 mode
      post.post.aa64el0 debug post.post.spe notFetch dcache pa1 mapped1 raw noUpd
    have tas2 := tas_of_current spec config rows mapping s (plus8 A) acc member2 data2 current access2 mode
      post.post.aa64el0 debug post.post.spe notFetch dcache pa2 mapped2 raw noUpd
    obtain ⟨u1, ad1, t11, x, u2, ad2, t21, t, fu1, call1, evx, rx, mx, fu2, call2, call, evt, rt, mt⟩ :=
      MemM1.MemPair8R.pair8_read A h8 h16 acc s pa1 pa2 value hA post lse2 tas1 tas2 mmio1 mmio2 bytes1 bytes2
    obtain ⟨ad1', t11', call1', _, _, _, _, _, _, _, _, traffic1⟩ := translate_noupdate_at spec config rows mapping
      ⟨A, ⟨acc, true⟩, ((8 : Nat) : Int)⟩ member1 data1 s u1 fu1.1 fu1.2.1 current access1 mode
      post.post.aa64el0 debug post.post.spe notFetch dcache pa1 mapped1 raw noUpd
    have same1 := call1.symm.trans call1'
    simp only [EStateM.Result.ok.injEq] at same1
    obtain ⟨rfl, rfl⟩ := same1
    obtain ⟨ad2', t21', call2', _, _, _, _, _, _, _, _, traffic2⟩ := translate_noupdate_at spec config rows mapping
      ⟨plus8 A, ⟨acc, true⟩, ((8 : Nat) : Int)⟩ member2 data2 s u2 (fu2.1.trans rx) (fu2.2.1.trans mx) current
      access2 mode post.post.aa64el0 debug post.post.spe notFetch dcache pa2 mapped2 raw noUpd
    have same2 := call2.symm.trans call2'
    simp only [EStateM.Result.ok.injEq] at same2
    obtain ⟨rfl, rfl⟩ := same2
    refine ⟨t, call, rt, mt, Or.inr ⟨h16, ad1, t11.events, ad2, t21.events, ?_, ?_, evt⟩⟩
    · rw [← fu1.2.2]; exact traffic1
    · rw [← evx, ← fu2.2.2]; exact traffic2

theorem storePair_noupdate {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : State) (A : BitVec 64) (h8 : A.toNat % 8 = 0) (acc : AccessDescriptor)
    (hA : MemM1.MemWriteD5.AccDWT acc) (pair : PairAccess spec config rows mapping A acc s)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : MemM1.MemReadD2.PostRegs2 s.regs) (preW : MemM1.MemWriteD6.PreW acc s.regs)
    (lse2 : s.regs.FeatureImpl[111] = true) (dcache : currentDCache s.regs = true)
    (pa1 pa2 : BitVec 56) (mapped1 : mapping A = some pa1.toNat) (mapped2 : mapping (plus8 A) = some pa2.toNat)
    (contiguous : A.toNat % 16 = 0 → pa2.toNat = pa1.toNat + 8)
    (mmio1 : MemM1.MemReadIF.NotMMIO pa1) (mmio2 : MemM1.MemReadIF.NotMMIO pa2)
    (outside1 : ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa1.toNat + i))
    (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (value : BitVec (16 * 8)) :
    ∃ t, Mem_set__1 A 16 acc true value s = .ok () t ∧ t.regs = s.regs ∧
      t.mem = MemM1.MemWriteD1.wfold (MemM1.MemWriteD1.wfold s.mem pa1.toNat 8 (fun j => value.extractLsb' (8 * j) 8))
        pa2.toNat 8 (fun j => value.extractLsb' (8 * (j + 8)) 8) ∧
      PairEvents spec A pa1 pa2
        (.memWrite pa1.toNat 16 (some A.toNat) MemM1.MemWriteD4.akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 16) value)) none)
        (.memWrite pa1.toNat 8 (some A.toNat) MemM1.MemWriteD4.akPlain (some (value.extractLsb' 0 64)) none)
        (.memWrite pa2.toNat 8 (some (plus8 A).toNat) MemM1.MemWriteD4.akPlain (some (value.extractLsb' 64 64)) none)
        s.events t.events := by
  have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hA.base.gpr]; rfl
  by_cases h16 : A.toNat % 16 = 0
  · obtain ⟨member, data, access⟩ := pair.1 h16
    obtain ⟨u, ad, t1, t, fu, tcall, call, events, regs, mem, _⟩ := MemM1.MemWriteD7.stp_lse2_strong A h16 acc s
      value hA pa1 preW post.post.spe lse2
      (fun u ur um => by
        obtain ⟨ad, t1, c, f, p, n, i, o, v, r, m, _⟩ := translate_noupdate_at spec config rows mapping
          ⟨A, ⟨acc, true⟩, ((16 : Nat) : Int)⟩ member data s u ur um current access mode post.post.aa64el0 debug
          post.post.spe notFetch dcache pa1 mapped1 raw noUpd
        exact ⟨ad, t1, c, f, p, n, i, o, v, r.trans ur.symm, m.trans um.symm⟩) mmio1
    obtain ⟨ad', t1', call', _, _, _, _, _, _, _, _, traffic⟩ := translate_noupdate_at spec config rows mapping
      ⟨A, ⟨acc, true⟩, ((16 : Nat) : Int)⟩ member data s u fu.1 fu.2.1 current access mode post.post.aa64el0 debug
      post.post.spe notFetch dcache pa1 mapped1 raw noUpd
    have same := tcall.symm.trans call'
    simp only [EStateM.Result.ok.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    refine ⟨t, call, regs, ?_, Or.inl ⟨h16, ad, t1.events, by rw [← fu.2.2]; exact traffic, events⟩⟩
    rw [mem]
    apply Std.ExtHashMap.ext_getElem?
    intro p
    have c := contiguous h16
    simp only [MemM1.MemWriteD1.wfold_get, c, MemM1.MemWriteD4.wbyte]
    by_cases r1 : pa1.toNat ≤ p ∧ p < pa1.toNat + 8
    · have r16 : pa1.toNat ≤ p ∧ p < pa1.toNat + 16 := by omega
      have n8 : ¬ (pa1.toNat + 8 ≤ p) := by omega
      simp only [r16, r1, n8, and_true, and_self, true_and, false_and, ↓reduceIte]
      first | rfl | simp [BitVec.castWidth]
    · by_cases r2 : pa1.toNat + 8 ≤ p ∧ p < pa1.toNat + 8 + 8
      · have r16 : pa1.toNat ≤ p ∧ p < pa1.toNat + 16 := by omega
        have y8 : pa1.toNat + 8 ≤ p := r2.1
        have y16 : p < pa1.toNat + 8 + 8 := r2.2
        simp only [r16, y8, y16, and_true, and_self, true_and, ↓reduceIte]
        have e : p - (pa1.toNat + 8) + 8 = p - pa1.toNat := by omega
        rw [e]
        first | rfl | simp [BitVec.castWidth]
      · have r16 : ¬ (pa1.toNat ≤ p ∧ p < pa1.toNat + 16) := by omega
        simp only [r16, r1, r2, ↓reduceIte]
  · obtain ⟨⟨member1, data1, access1⟩, ⟨member2, data2, access2⟩⟩ := pair.2 h16
    have strong1 := strongTA_of_current spec config rows mapping s A acc member1 data1 current access1 mode
      post.post.aa64el0 debug post.post.spe notFetch dcache pa1 mapped1 raw noUpd
    have strong2 : ∀ s1 : State, s1.regs = s.regs →
        s1.mem = MemM1.MemWriteD1.wfold s.mem pa1.toNat 8 (fun j => value.extractLsb' (8 * j) 8) →
        MemM1.MemWriteD7.StrongTA (plus8 A) acc 8 pa2 s1 := by
      intro s1 hr hm
      obtain ⟨current1, raw1⟩ := current_after_store8 current raw pa1 _ outside1 hr hm
      exact strongTA_of_current spec config rows mapping s1 (plus8 A) acc member2 data2 current1
        (access2.of_regs hr) (by rw [hr]; exact mode) (by rw [hr]; exact post.post.aa64el0)
        (by rw [hr]; exact debug) (by rw [hr]; exact post.post.spe) notFetch (by rw [hr]; exact dcache)
        pa2 mapped2 raw1 (by rw [hr]; exact noUpd)
    obtain ⟨u1, ad1, t11, x, u2, ad2, t21, t, fu1, call1, evx, rx, mx, fu2, call2, call, evt, rt, mt⟩ :=
      MemM1.MemPair8W.pair8_set A h8 h16 acc s value hA pa1 pa2 preW post.post.spe lse2 strong1 strong2 mmio1 mmio2
    obtain ⟨ad1', t11', call1', _, _, _, _, _, _, _, _, traffic1⟩ := translate_noupdate_at spec config rows mapping
      ⟨A, ⟨acc, true⟩, ((8 : Nat) : Int)⟩ member1 data1 s u1 fu1.1 fu1.2.1 current access1 mode
      post.post.aa64el0 debug post.post.spe notFetch dcache pa1 mapped1 raw noUpd
    have same1 := call1.symm.trans call1'
    simp only [EStateM.Result.ok.injEq] at same1
    obtain ⟨rfl, rfl⟩ := same1
    obtain ⟨currentX, rawX⟩ := current_after_store8 current raw pa1 _ outside1 rx mx
    obtain ⟨ad2', t21', call2', _, _, _, _, _, _, _, _, traffic2⟩ := translate_noupdate_at spec config rows mapping
      ⟨plus8 A, ⟨acc, true⟩, ((8 : Nat) : Int)⟩ member2 data2 x u2 fu2.1 fu2.2.1 currentX (access2.of_regs rx)
      (by rw [rx]; exact mode) (by rw [rx]; exact post.post.aa64el0) (by rw [rx]; exact debug)
      (by rw [rx]; exact post.post.spe) notFetch (by rw [rx]; exact dcache) pa2 mapped2 rawX (by rw [rx]; exact noUpd)
    have same2 := call2.symm.trans call2'
    simp only [EStateM.Result.ok.injEq] at same2
    obtain ⟨rfl, rfl⟩ := same2
    refine ⟨t, call, rt, by rw [mt, mx], Or.inr ⟨h16, ad1, t11.events, ad2, t21.events, ?_, ?_, evt⟩⟩
    · rw [← fu1.2.2]; exact traffic1
    · rw [← evx, ← fu2.2.2]; exact traffic2

#print axioms loadPair_noupdate
#print axioms storePair_noupdate
end ArmCertWalk
