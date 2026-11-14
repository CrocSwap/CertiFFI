import M1a.J3c
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a.TWP
abbrev State := SequentialState Regs oracleChoiceSource
open S1OuterSetup S1LogicalReference ArmCert.Eval.JointSAT ArmCert.Eval.M1a

/- translate_walk_path: memory's WalkFact for a general lower VA from a
   logical Path from the actual TTBR0_EL2 root to a level-3 page leaf. All hypotheses are stated
   on the registers and memory of s; none mentions the oracle-drawn walk parameters (the EL20
   Get fixes them: Fields (ee = pie = 0, ha = hd = 1) and Active (4K, txsz 16, ps 5)). -/



/-- The EL2&0 lower-range root table base from the registers (start level 0). -/
def rootOf (r : Regs) (va : BitVec 64) : BitVec 56 :=
  Align_bits (Sail.BitVec.updateSubrange (0#56) 47 1
    (Sail.BitVec.extractLsb (S1EntryRoot.word r .Regime_EL20 va) 47 1))
    (_shl_int_general 1 (48 - ((3 - 0) * 9 + 12) + 3))

/-- The root slot address for va. -/
def rootSlot (r : Regs) (va : BitVec 64) : FullAddress :=
  S1InitialEntryAddress.address va {address := rootOf r va, paspace := .PAS_NonSecure}

theorem base_eq (wp : S1TTWParams) (r : Regs) (va : BitVec 64) (hd : wp.d128 = 0#1)
    (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6) :
    S1EntryRoot.base wp r .Regime_EL20 va = rootOf r va := by
  unfold S1EntryRoot.base rootOf
  rw [S1EntryCallees.start_zero wp hd htg htx]

theorem bytes_unique (mem : Nat → Option (BitVec 8)) (p : FullAddress) (d d' : BitVec 64)
    (h1 : BytesAt false mem p d) (h2 : BytesAt false mem p d') : d = d' := by
  have hb : ∀ i < 8, byte false d i = byte false d' i :=
    fun i hi => Option.some.inj ((h1 i hi).symm.trans (h2 i hi))
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := congrArg (fun x : BitVec 8 => x.getLsbD (j % 8)) (hb (j / 8) (by omega))
  have l : j % 8 < 8 := by omega
  have e : 8 * (j / 8) + j % 8 = j := by omega
  simp only [byte, Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_extractLsb', l,
    decide_true, Bool.true_and, e] at h
  exact h

/-- memory's WalkFact (MemM1.ConsumerV/WalkFactV), restated here verbatim. -/
def WalkFact (s : State) (va : BitVec 64) (D : BitVec 64) : Prop :=
  ∀ t : State, t.regs = s.regs → t.mem = s.mem →
    ∀ (f : FaultRecord) (acc' : AccessDescriptor), f.statuscode = .Fault_None →
      acc'.ss = .SS_NonSecure →
      ∃ (wp : S1TTWParams) (u : State),
        AArch64_GetS1TTWParams .Regime_EL20 acc'.ss va t = .ok wp u ∧
        S1Normality.Frame t u ∧ EL20.Fields.Fields wp ∧ EL20.Active wp ∧
        ∀ v : State, v.regs = t.regs → v.mem = t.mem →
          ∃ (c : Context) (r : FaultRecord × AddressDescriptor × TTWState × BitVec 64)
            (w : State), c.wp = wp ∧ c.acc = acc' ∧ c.va = va ∧ c.regime = .Regime_EL20 ∧
            AArch64_S1Walk f wp va .Regime_EL20 acc' 64 v = .ok r w ∧ PostR c v D r w


#print axioms base_eq
#print axioms bytes_unique
end ArmCert.Eval.M1a.TWP
