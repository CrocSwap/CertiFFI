import ArmCertTranslateModel.Readiness

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- `leaf=true` denotes a leaf use of a physical slot; false denotes a table
    use. Roles attach to observations, so a slot can serve both kinds of path. -/
abbrev RoleObservation := Nat → Bool → S1DescriptorPIE.View 64 → Prop

def RoleReady (ha leaf : Bool) (d : BitVec 64) : Prop :=
  leaf = true → DescriptorDelta.AFReady ha d

/-- A current byte-contents invariant, with no source-result or future-state
    conjunct. A false-role observation places no AF=1 requirement on a table. -/
def ImageRealizes (observe : RoleObservation) (pie ha hd : Bool) (mem : Mem) : Prop :=
  ∀ slot leaf view, observe slot leaf view →
    ∃ d, S1ByteMemory.DescAt mem slot d ∧ S1DescriptorPIE.view pie ha hd d = view ∧ RoleReady ha leaf d

def ImageCovers (observe : RoleObservation) (f : Footprint) : Prop :=
  ∀ slot leaf view, observe slot leaf view → slot ∈ f.slots

def ImageAligned (observe : RoleObservation) : Prop :=
  ∀ slot leaf view, observe slot leaf view → slot % 8 = 0

/-- AF is monotone under the actual source word update, independently of which
    role's control authorized it. In particular, HAFT need not equal leaf HA. -/
theorem source_af_mono (af dirty : Bool) (d : BitVec 64) (h : d.getLsbD 10 = true) :
    (S1Descriptor.hardwareUpdate af dirty d).getLsbD 10 = true := by
  cases af <;> cases dirty
  · exact h
  · change (S1Descriptor.setDirty d).getLsbD 10 = true
    rw [S1Descriptor.setDirty_other d 10 (by decide)]
    exact h
  · exact setAF_bit d
  · change (S1Descriptor.setDirty (S1Descriptor.setAF d)).getLsbD 10 = true
    rw [S1Descriptor.setDirty_other _ 10 (by decide)]
    exact setAF_bit d

theorem RoleReady.hardware (h : RoleReady ha leaf d) (af dirty : Bool) :
    RoleReady ha leaf (S1Descriptor.hardwareUpdate af dirty d) := by
  intro hl
  exact (h hl).elim (fun hf => Or.inl (source_af_mono af dirty d hf)) Or.inr

/-- Physical separation preserves every table/leaf use, including shared slots. -/
theorem ImageRealizes.program_write (h : ImageRealizes observe pie ha hd mem)
    (f : Footprint) (hwidth : f.width = 8) (hc : ImageCovers observe f)
    (hf : WritesOnly writes (fun a => mem[a]?) (fun a => mem'[a]?))
    (hs : Separated f.byte writes) : ImageRealizes observe pie ha hd mem' := by
  intro slot leaf view ho
  obtain ⟨d, hb, hv, hr⟩ := h slot leaf view ho
  refine ⟨d, ?_, hv, hr⟩
  intro i hi
  have hi' : i < f.width := by simpa only [hwidth] using hi
  exact (table_unchanged hf hs _ (f.covers slot (hc slot leaf view ho) ⟨i, hi'⟩)).trans (hb i hi)

/-- Arbitrary table/leaf aliases are preserved by the actual source-compatible
    update. No role-uniqueness or exclusion of program read aliases is assumed. -/
theorem ImageRealizes.hardware_store (h : ImageRealizes observe pie ha hd mem)
    (hslots : ImageAligned observe) (slot : Nat) (d : BitVec 64) (af dirty : Bool)
    (hAlign : slot % 8 = 0) (hDesc : S1ByteMemory.DescAt mem slot d)
    (hDirty : dirty = true → ha = true ∧ hd = true ∧
      (pie = false → d.getLsbD 51 = true)) :
    ImageRealizes observe pie ha hd (S1ByteMemory.store mem slot (S1Descriptor.hardwareUpdate af dirty d)) := by
  intro b leaf view ho
  obtain ⟨old, hb, hv, hr⟩ := h b leaf view ho
  by_cases heq : slot = b
  · subst b
    have hd : old = d := S1ByteMemory.descriptor_unique mem slot old d hb hDesc
    subst old
    exact ⟨_, S1ByteMemory.stored_descriptor _ _ _,
      (S1DescriptorPIE.hardware_view pie ha hd af dirty d hDirty).trans hv, hr.hardware af dirty⟩
  · exact ⟨old, S1ByteMemory.other_descriptor mem slot b _ old hAlign (hslots b leaf view ho) heq hb, hv, hr⟩

/-- Actual swap existence and readiness/realization preservation are proved
    together. The role-specific caller may authorize table AF through HAFT even
    when leaf HA is false; this result does not conflate those controls. -/
theorem swap_image_preserves (pie ha hd af dirty : Bool)
    (fault : FaultRecord) (d : BitVec 64) (acc : AccessDescriptor)
    (addr : AddressDescriptor) (ti : TranslationInfo) (s : State)
    (f : Footprint) (observe : RoleObservation)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hRAM : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (hAlign : addr.paddress.address.toNat % 8 = 0)
    (hDesc : S1ByteMemory.DescAt s.mem addr.paddress.address.toNat d)
    (hDirty : dirty = true → ha = true ∧ hd = true ∧
      (pie = false → d.getLsbD 51 = true))
    (hWidth : f.width = 8) (hSlot : addr.paddress.address.toNat ∈ f.slots)
    (hAligned : ImageAligned observe)
    (hReal : ImageRealizes observe pie ha hd s.mem) :
    ∃ t : State,
      AArch64_MemSwapTableDesc fault d (S1Descriptor.hardwareUpdate af dirty d)
        0#1 acc addr ti s = .ok (fault, S1Descriptor.hardwareUpdate af dirty d) t ∧
      t.regs = s.regs ∧ ImageRealizes observe pie ha hd t.mem ∧
      WritesOnly f.byte (fun a => s.mem[a]?) (fun a => t.mem[a]?) := by
  have hzero : (0#1 : BitVec 1) ≠ 1#1 := by decide
  have hdesc' : S1ByteMemory.DescAt s.mem addr.paddress.address.toNat (S2Endian.encode 0#1 d) := by
    simpa only [S2Endian.encode, hzero, ↓reduceIte] using hDesc
  obtain ⟨t, ht, hregs, _, hframe⟩ := S1HardwareSwap.complete 0#1 pie ha hd af dirty fault d acc addr ti s
    hNoRME hRAM hAlign hdesc' hDirty
  have hdesc2 : S2ByteMemory.DescAt s.mem addr.paddress.address.toNat (S2Endian.encode 0#1 d) := by
    intro i hi
    simpa only [S2Endian.encode, hzero, ↓reduceIte] using hDesc i hi
  have he := S2SwapAnyFrame.effect 0#1 fault d (S1Descriptor.hardwareUpdate af dirty d) acc addr ti s hNoRME hRAM hdesc2
  rw [ht] at he
  have hm := he.2.2.2
  simp only [S2Endian.encode, hzero, ↓reduceIte] at hm
  change t.mem = S1ByteMemory.store s.mem addr.paddress.address.toNat (S1Descriptor.hardwareUpdate af dirty d) at hm
  refine ⟨t, ht, hregs, ?_, ?_⟩
  · rw [hm]
    exact hReal.hardware_store hAligned _ d af dirty hAlign hDesc hDirty
  · intro a ha
    apply hframe
    by_cases hlo : a < addr.paddress.address.toNat
    · exact Or.inl hlo
    · right
      have hn : ¬ a < addr.paddress.address.toNat + 8 := by
        intro hi
        exact ha ⟨addr.paddress.address.toNat, hSlot, by omega, by simpa only [hWidth] using hi⟩
      omega

#print axioms ImageRealizes.program_write
#print axioms ImageRealizes.hardware_store
#print axioms swap_image_preserves
end ArmCert.Translate.Model
