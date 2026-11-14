-- Memory classes: one data translation from the canonical invariant under the
-- decision-171 no-update route, in the shape the SDK MemM1 read/write skeletons consume
-- (hTA / hE'), plus the ordered actual translation traffic.
import ArmCertWalk.DataAccessEvents
import MemM1.MemReadD2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
namespace ArmCertWalk

/-- Actual no-update translation traffic from `before` to `after` ending with `translationEnd ad`. -/
def NoUpdateTraffic {domain : QueryDomain} (spec : TopologyImageSpec domain) (va : BitVec 64)
    (before : Array Event) (ad : AddressDescriptor) (after : Array Event) : Prop :=
  ∃ (info : TranslationStartInfo) (walk : List (Nat × Bool × Array Event))
    (leaf : Nat × Bool × Array Event) (middle : Array Event),
    TranslateTrafficFrom (before.push (.translationStart info)) walk leaf middle ∧
    (∀ step ∈ walk, step.2.1 = false) ∧ leaf.2.1 = false ∧
    ((spec.logicalRows.map (·.logical)).Nodup → walk.map (·.1) = declaredSlots spec.logicalRows spec.layout va) ∧
    after = middle.push (.translationEnd ad)

theorem translate_noupdate_at {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (q : AccessQuery) (member : domain q) (data : S1AccessData spec config rows q)
    (s u : State) (uRegs : u.regs = s.regs) (uMem : u.mem = s.mem)
    (current : CurrentS1At spec config rows s)
    (access : CurrentS1AccessAt spec config rows mapping q data s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (notFetch : (q.request.raw.acctype == .AccessType_IFETCH) = false)
    (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping q.va = some pa.toNat)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : NoUpdateRows {spec.params with haft := hostHAFT s.regs} q.request.raw spec.imageRows = true) :
    ∃ ad t1, AArch64_TranslateAddress q.va q.request.raw q.request.aligned q.size u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress = { paspace := .PAS_NonSecure, address := pa } ∧
      ad.memattrs.memtype = .MemType_Normal ∧
      ad.memattrs.inner.attrs = MemAttr_WB ∧ ad.memattrs.outer.attrs = MemAttr_WB ∧
      ad.vaddress = q.va ∧ t1.regs = s.regs ∧ t1.mem = s.mem ∧
      NoUpdateTraffic spec q.va u.events ad t1.events := by
  obtain ⟨address, fault, other, call, fields, _, _, _, _, _, _, _, _, _,
      info, walk, leaf, middle, _, traffic, endEv, cond, wb, slots⟩ :=
    current_translate_address_events spec config rows mapping q member data u
      (current_s1_frame current uRegs uMem) (access.of_regs uRegs)
      (by rw [uRegs]; exact mode) (by rw [uRegs]; exact aa64)
      (by rw [uRegs]; exact debug) (by rw [uRegs]; exact spe)
  obtain ⟨_, out, _, _, _, _, _, mapResult, vaddr, normal, addressFault, nonsecure, _, registers, _⟩ := fields
  have addressPA : address.paddress.address = pa :=
    BitVec.eq_of_toNat_eq (Option.some.inj (mapResult.symm.trans mapped))
  have otherRegs : other.regs = s.regs := by
    rw [registers, uRegs]; unfold fetchGuardRegs; simp only [notFetch, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨walkFlags, leafFlag, otherMem⟩ := cond (by rw [uMem]; exact raw) (by rw [uRegs]; exact none)
  have cached : outputCached q.request.raw u.regs = true := by
    unfold outputCached; rw [notFetch, uRegs]; exact dcache
  obtain ⟨inner, outer⟩ := wb cached
  have paddr : address.paddress = { paspace := .PAS_NonSecure, address := pa } := by
    cases h : address.paddress with
    | mk space addr =>
      rw [h] at addressPA nonsecure
      simp only at addressPA nonsecure
      rw [addressPA, nonsecure]
  exact ⟨address, other, call, addressFault, paddr, normal, inner, outer, vaddr, otherRegs,
    otherMem.trans uMem, info, walk, leaf, middle, traffic, walkFlags, leafFlag, slots, endEv⟩

#print axioms translate_noupdate_at

/-- LSE2 16-byte aligned load (`Mem_read__1 A 16 acc true`) from the canonical invariant,
no-update route; registers and memory unchanged, events = no-update traffic then the read. -/
theorem load16_noupdate {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : State) (A : BitVec 64) (halign : A.toNat % 16 = 0) (acc : AccessDescriptor)
    (hA : MemM1.MemReadD2.AccDR2 acc)
    (member : domain ⟨A, ⟨acc, true⟩, ((16 : Nat) : Int)⟩)
    (data : S1AccessData spec config rows ⟨A, ⟨acc, true⟩, ((16 : Nat) : Int)⟩)
    (current : CurrentS1At spec config rows s)
    (access : CurrentS1AccessAt spec config rows mapping ⟨A, ⟨acc, true⟩, ((16 : Nat) : Int)⟩ data s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : MemM1.MemReadD2.PostRegs2 s.regs) (lse2 : s.regs.FeatureImpl[111] = true)
    (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping A = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (value : BitVec (16 * 8)) (bytes : ∀ i < 16, s.mem[pa.toNat + i]? = some (value.extractLsb' (8 * i) 8)) :
    ∃ ad mid t, Mem_read__1 A 16 acc true s = .ok value t ∧ NoUpdateTraffic spec A s.events ad mid ∧
      ad.vaddress = A ∧
      t.events = mid.push (.memRead pa.toNat 16 (some A.toNat) (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = s.regs ∧ t.mem = s.mem := by
  have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hA.gpr]; rfl
  obtain ⟨ad, t1, t, ⟨t1Regs, t1Mem, vaddr, traffic⟩, call, events, regs, mem⟩ :=
    MemM1.MemReadD2.memReadPair A halign acc s pa value hA post.noMTE2 lse2
      (fun ad t1 => t1.regs = s.regs ∧ t1.mem = s.mem ∧ ad.vaddress = A ∧
        NoUpdateTraffic spec A s.events ad t1.events)
      (by
        intro u fu
        obtain ⟨ad, t1, call, fault, paddr, normal, inner, outer, vaddr, r, m, traffic⟩ :=
          translate_noupdate_at spec config rows mapping ⟨A, ⟨acc, true⟩, ((16 : Nat) : Int)⟩ member data s u
            fu.1 fu.2.1 current access mode post.post.aa64el0 debug post.post.spe notFetch dcache pa mapped raw noUpd
        refine ⟨ad, t1, call, fault, by rw [paddr], normal, inner, outer, by rw [r]; exact post, ?_,
          r, m, vaddr, by rw [← fu.2.2]; exact traffic⟩
        intro i hi
        rw [m]; exact bytes i hi)
      mmio
  refine ⟨ad, t1.events, t, call, traffic, vaddr, ?_, regs.trans t1Regs, mem.trans t1Mem⟩
  rw [events, vaddr]

#print axioms load16_noupdate
end ArmCertWalk
