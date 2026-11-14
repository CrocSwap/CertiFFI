import MemM1.MemDataV3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
namespace MemM1.MemDataV5
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2 MemM1.MemWriteD1 MemM1.MemWriteD4
open MemM1.MemWriteD5 MemM1.MemWriteD6 MemM1.MemWriteD7 MemM1.MemDataV3
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2
open ArmCert.Premises.TranslationAgreesV3 (TTWReadsOK DataPins)

/-! `MemDataV3` on step-boundary-v2 v5, where `DataPins` carries `mte2Off` (FeatureImpl[134] =
false) and `lse2` (FeatureImpl[111] = true): the MTE2 and LSE2 hypotheses are taken from
`DataPins`. The only extra register hypothesis left is `BEPins` (BigEndian inputs). -/

theorem postRegs2_v5 (s : State) (hD : DataPins s) (hB : BEPins s.regs) : PostRegs2 s.regs :=
  postRegs2_of s hD hB hD.mte2Off

theorem preW_v5 (acc : AccessDescriptor) (s : State) (hD : DataPins s) (hB : BEPins s.regs) :
    PreW acc s.regs :=
  preW_of acc s hD hB hD.mte2Off

theorem postW_v5 (acc : AccessDescriptor) (s : State) (hD : DataPins s) : PostW acc s.regs :=
  postW_of acc s hD hD.mte2Off

/-- **LDRB (`Mem_read a 1 acc`) on E17 v3 + DataPins v5**, events fully pinned. -/
theorem readV5_ldrb (m : ConsumerMap) (walk : BitVec 64 → List Nat) (s : State)
    (hT : AgreesV3 m walk s) (hD : DataPins s) (hB : BEPins s.regs)
    (a : BitVec 64) (acc : AccessDescriptor) (hA : AccDR2 acc)
    (hp : m.permitted a acc true ((1 : Nat) : Int)) (hio : NotMMIO (m.pa a))
    (data : BitVec (1 * 8))
    (hmem : ∀ i < 1, s.mem[(m.pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ ad ti W t, Mem_read a 1 acc s = .ok data t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memRead (m.pa a).toNat 1 (some a.toNat)
          (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false] ∧
      TTWReadsOK walk a W ∧ t.regs = s.regs ∧ t.mem = s.mem :=
  readV3_ldrb m walk s hT hD hB hD.mte2Off a acc hA hp hio data hmem

/-- **LDP 64-bit (`Mem_read__1 a 16 acc true`, LSE2 from DataPins) on E17 v3 + DataPins v5**. -/
theorem readV5_ldp (m : ConsumerMap) (walk : BitVec 64 → List Nat) (s : State)
    (hT : AgreesV3 m walk s) (hD : DataPins s) (hB : BEPins s.regs)
    (a : BitVec 64) (halign : a.toNat % 16 = 0) (acc : AccessDescriptor) (hA : AccDR2 acc)
    (hp : m.permitted a acc true ((16 : Nat) : Int)) (hio : NotMMIO (m.pa a))
    (data : BitVec (16 * 8))
    (hmem : ∀ i < 16, s.mem[(m.pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ ad ti W t, Mem_read__1 a 16 acc true s = .ok data t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memRead (m.pa a).toNat 16 (some a.toNat)
          (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false] ∧
      TTWReadsOK walk a W ∧ t.regs = s.regs ∧ t.mem = s.mem :=
  readV3_ldp_lse2 m walk s hT hD hB hD.mte2Off hD.lse2 a halign acc hA hp hio data hmem

/-- **STRB (`Mem_set a 1 acc v`) on E17 v3 + DataPins v5**, events fully pinned. -/
theorem strbV5 (m : ConsumerMap) (walk : BitVec 64 → List Nat) (s : State)
    (hT : AgreesV3 m walk s) (hD : DataPins s) (hB : BEPins s.regs)
    (a : BitVec 64) (acc : AccessDescriptor) (v : BitVec (1 * 8)) (hA : AccDWT acc)
    (hp : m.permitted a acc true ((1 : Nat) : Int)) (hio : NotMMIO (m.pa a)) :
    ∃ ad ti W t, Mem_set a 1 acc v s = .ok () t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memWrite (m.pa a).toNat 1 (some a.toNat) akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 1) v)) none] ∧
      TTWReadsOK walk a W ∧ t.regs = s.regs ∧
      t.mem = wfold s.mem (m.pa a).toNat 1 (wbyte v) ∧
      (∀ p, t.mem[p]? = if (m.pa a).toNat ≤ p ∧ p < (m.pa a).toNat + 1
        then some (wbyte v (p - (m.pa a).toNat)) else s.mem[p]?) :=
  strbV3 m walk s hT hD hB hD.mte2Off a acc v hA hp hio

/-- **STP 64-bit (`Mem_set__1 a 16 acc true v`, LSE2 from DataPins) on E17 v3 + DataPins v5**. -/
theorem stpV5 (m : ConsumerMap) (walk : BitVec 64 → List Nat) (s : State)
    (hT : AgreesV3 m walk s) (hD : DataPins s) (hB : BEPins s.regs)
    (a : BitVec 64) (ha : a.toNat % 16 = 0) (acc : AccessDescriptor) (v : BitVec (16 * 8))
    (hA : AccDWT acc)
    (hp : m.permitted a acc true ((16 : Nat) : Int)) (hio : NotMMIO (m.pa a)) :
    ∃ ad ti W t, Mem_set__1 a 16 acc true v s = .ok () t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memWrite (m.pa a).toNat 16 (some a.toNat) akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 16) v)) none] ∧
      TTWReadsOK walk a W ∧ t.regs = s.regs ∧
      t.mem = wfold s.mem (m.pa a).toNat 16 (wbyte v) ∧
      (∀ p, t.mem[p]? = if (m.pa a).toNat ≤ p ∧ p < (m.pa a).toNat + 16
        then some (wbyte v (p - (m.pa a).toNat)) else s.mem[p]?) :=
  stpV3_lse2 m walk s hT hD hB hD.mte2Off hD.lse2 a ha acc v hA hp hio

#print axioms postRegs2_v5
#print axioms preW_v5
#print axioms postW_v5
#print axioms readV5_ldrb
#print axioms readV5_ldp
#print axioms strbV5
#print axioms stpV5
end MemM1.MemDataV5
