import JointEL10.Get20
import JointEL10.Regime20
import GetEntry.PathTotal
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.JointSAT.J3
open S1OuterSetup S1LogicalReference GuestSetup ArmCert.Eval.JointSAT

/- a design decision: J3 = normal-path witness only (fault outcomes: backlog 48).
 Label: non-vacuity witness under implementation profile; not
   power-on reachability. One loader-written 8-byte descriptor at B is a
   self-referencing table for VA 0: levels 0..2 read it as a table, level 3 as
   a page. Its bytes are a palindrome, so it encodes the same descriptor under
   either endianness (wp.ee stays symbolic). -/
def B : Nat := 0x101000000
def desc : BitVec 64 := 0x0300000101000003#64

theorem palin (i : Nat) (hi : i < 8) : byte true desc i = byte false desc i := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

def loadDesc (m : Std.ExtHashMap Nat (BitVec 8)) : Std.ExtHashMap Nat (BitVec 8) :=
  ((((((((m.insert (B + 0) (byte false desc 0)).insert (B + 1) (byte false desc 1)).insert
    (B + 2) (byte false desc 2)).insert (B + 3) (byte false desc 3)).insert
    (B + 4) (byte false desc 4)).insert (B + 5) (byte false desc 5)).insert
    (B + 6) (byte false desc 6)).insert (B + 7) (byte false desc 7))

theorem load_get (m : Std.ExtHashMap Nat (BitVec 8)) (i : Nat) (hi : i < 8) :
    (loadDesc m)[B + i]? = some (byte false desc i) := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [loadDesc, B, Nat.reduceAdd, Std.ExtHashMap.getElem?_insert, Nat.reduceBEq,
      Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]

/-- Loader step before the register setup: table bytes plus TTBR0_EL1 (both views). -/
def tablePrep (s : State) : State :=
  {s with mem := loadDesc s.mem,
          regs := (Regs.ref_BitVec_128 ._TTBR0_EL1).set (BitVec.ofNat 128 B)
            ((Regs.ref_BitVec_64 .TTBR0_NS).set (BitVec.ofNat 64 B) s.regs)}

theorem prep_tlb (s : State) :
    (tablePrep s).regs.bank_Bool .__tlb_enabled = s.regs.bank_Bool .__tlb_enabled := by
  simp [tablePrep, Regs.ref_BitVec_64, Regs.ref_BitVec_128, RegMap.set]

theorem prep_mem (s : State) : (tablePrep s).mem = loadDesc s.mem := by
  dsimp only [tablePrep]


theorem prep_ttbr (s : State) :
    (tablePrep s).regs.bank_BitVec_128 ._TTBR0_EL1 = BitVec.ofNat 128 B ∧
      (tablePrep s).regs.bank_BitVec_64 .TTBR0_NS = BitVec.ofNat 64 B := by
  simp [tablePrep, Regs.ref_BitVec_64, Regs.ref_BitVec_128, RegMap.set]

def phys : FullAddress := {paspace := .PAS_NonSecure, address := BitVec.ofNat 56 B}

def noFault : FaultRecord := {(default : FaultRecord) with statuscode := .Fault_None}




/-- Loader step for EL2&0 (lower range): table bytes plus TTBR0_EL2 (both views). -/
def tablePrep20 (s : State) : State :=
  {s with mem := loadDesc s.mem,
          regs := (Regs.ref_BitVec_128 ._TTBR0_EL2).set (BitVec.ofNat 128 B)
            ((Regs.ref_BitVec_64 .HTTBR).set (BitVec.ofNat 64 B) s.regs)}

theorem prep20_tlb (s : State) :
    (tablePrep20 s).regs.bank_Bool .__tlb_enabled = s.regs.bank_Bool .__tlb_enabled := by
  simp [tablePrep20, Regs.ref_BitVec_64, Regs.ref_BitVec_128, RegMap.set]

theorem prep20_mem (s : State) : (tablePrep20 s).mem = loadDesc s.mem := by
  dsimp only [tablePrep20]

theorem prep20_ttbr (s : State) :
    (tablePrep20 s).regs.bank_BitVec_128 ._TTBR0_EL2 = BitVec.ofNat 128 B ∧
      (tablePrep20 s).regs.bank_BitVec_64 .HTTBR = BitVec.ofNat 64 B := by
  simp [tablePrep20, Regs.ref_BitVec_64, Regs.ref_BitVec_128, RegMap.set]


end ArmCert.Eval.JointSAT.J3
