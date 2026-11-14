-- Actual prepared-descriptor access packets and bounded oracle transport.
import NativeAccess.Trace
import NativeMteTagCheck.Transport
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false
namespace TranslateSpan.DefaultAccessTrace
abbrev State := NativeMteTagCheck.State
open S1Normality MemM1.MemReadIF MemM1.MemWriteD1
open NativeAccess.Trace (Access NormalWB)
open NativeMteTagCheck
open NativeMteTagCheck.StatusTrace (TraceFrame)

/-- Actual translation and call witnesses. No virtual/physical contiguity
across different calls, admission alignment, or future callback is stored. -/
structure ReadPacket (r : Access) (before : State) where
  data : BitVec (r.bytes * 8)
  translationInput : State
  translated : State
  after : State
  ad : AddressDescriptor
  walkEvents : Array Event
  prepared : AccessDescriptor
  preparedShape : prepared = { r.acc with tagchecked := prepared.tagchecked }
  choiceFrame : TraceFrame before translationInput
  translation : AArch64_TranslateAddress r.va prepared r.aligned (r.bytes : Int)
    translationInput = .ok ad translated
  sizeOK : SizeOK r.bytes
  ram : NotMMIO ad.paddress.address
  noFault : ad.fault.statuscode = .Fault_None
  normalWB : NormalWB ad
  translationRegs : translated.regs = before.regs
  translationMem : translated.mem = before.mem
  translationEvents : translated.events = before.events ++ walkEvents
  draws : Nat
  choice : ChoiceDelta before after draws
  drawBound : draws ≤ 1
  run : r.read before = .ok data after
  regs : after.regs = translated.regs
  mem : after.mem = translated.mem
  events : after.events = translated.events.push (.memRead ad.paddress.address.toNat r.bytes
    (some ad.vaddress.toNat) (AccessDescriptor_to_Access_kind r.acc) false)

structure WritePacket (r : Access) (before : State) where
  data : BitVec (r.bytes * 8)
  translationInput : State
  translated : State
  after : State
  ad : AddressDescriptor
  walkEvents : Array Event
  prepared : AccessDescriptor
  preparedShape : prepared = { r.acc with tagchecked := prepared.tagchecked }
  choiceFrame : TraceFrame before translationInput
  translation : AArch64_TranslateAddress r.va prepared r.aligned (r.bytes : Int)
    translationInput = .ok ad translated
  sizeOK : SizeOK r.bytes
  ram : NotMMIO ad.paddress.address
  noFault : ad.fault.statuscode = .Fault_None
  normalWB : NormalWB ad
  translationRegs : translated.regs = before.regs
  translationMem : translated.mem = before.mem
  translationEvents : translated.events = before.events ++ walkEvents
  draws : Nat
  choice : ChoiceDelta before after draws
  drawBound : draws ≤ 1
  run : r.write data before = .ok () after
  regs : after.regs = translated.regs
  mem : after.mem = wfold translated.mem ad.paddress.address.toNat r.bytes
    (fun j => (Sail.BitVec.castWidth (m := 8 * r.bytes) data).extractLsb' (8 * j) 8)
  events : after.events = translated.events.push (.memWrite ad.paddress.address.toNat r.bytes
    (some ad.vaddress.toNat) (AccessDescriptor_to_Access_kind r.acc)
    (some (Sail.BitVec.castWidth (m := 8 * r.bytes) data)) none)

theorem ReadPacket.memory {r : Access} {s : State} (p : ReadPacket r s) :
    p.after.mem = s.mem := p.mem.trans p.translationMem

theorem ReadPacket.registers {r : Access} {s : State} (p : ReadPacket r s) :
    p.after.regs = s.regs := p.regs.trans p.translationRegs

theorem WritePacket.memory {r : Access} {s : State} (p : WritePacket r s) :
    p.after.mem = wfold s.mem p.ad.paddress.address.toNat r.bytes
      (fun j => (Sail.BitVec.castWidth (m := 8 * r.bytes) p.data).extractLsb' (8 * j) 8) := by
  rw [p.mem,p.translationMem]

theorem WritePacket.registers {r : Access} {s : State} (p : WritePacket r s) :
    p.after.regs = s.regs := p.regs.trans p.translationRegs

/-- Physical-event block includes the actual translation events. -/
def ReadPacket.block {r : Access} {s : State} (p : ReadPacket r s) : Array Event :=
  p.walkEvents.push (.memRead p.ad.paddress.address.toNat r.bytes (some p.ad.vaddress.toNat)
    (AccessDescriptor_to_Access_kind r.acc) false)

def WritePacket.block {r : Access} {s : State} (p : WritePacket r s) : Array Event :=
  p.walkEvents.push (.memWrite p.ad.paddress.address.toNat r.bytes (some p.ad.vaddress.toNat)
    (AccessDescriptor_to_Access_kind r.acc)
    (some (Sail.BitVec.castWidth (m := 8 * r.bytes) p.data)) none)

theorem ReadPacket.events_block {r : Access} {s : State} (p : ReadPacket r s) :
    p.after.events = s.events ++ p.block := by
  rw [p.events,p.translationEvents,Array.push_append]
  rfl

theorem WritePacket.events_block {r : Access} {s : State} (p : WritePacket r s) :
    p.after.events = s.events ++ p.block := by
  rw [p.events,p.translationEvents,Array.push_append]
  rfl

structure ReadCall where
  request : Access
  before : State
  packet : ReadPacket request before

structure WriteCall where
  request : Access
  before : State
  packet : WritePacket request before

/-- These are intermediate effect witnesses. A final root must derive the
chain from its actual Sail path; the frame bridges justify actual control
bookkeeping and do not identify complete states or supply future executions. -/
inductive ReadChain : State → List ReadCall → State → Prop where
  | nil {s t : State} (frame : TraceFrame s t) : ReadChain s [] t
  | cons {s t : State} (c : ReadCall) {cs : List ReadCall}
      (frame : TraceFrame s c.before) (tail : ReadChain c.packet.after cs t) : ReadChain s (c :: cs) t

inductive WriteChain : State → List WriteCall → State → Prop where
  | nil {s t : State} (frame : TraceFrame s t) : WriteChain s [] t
  | cons {s t : State} (c : WriteCall) {cs : List WriteCall}
      (frame : TraceFrame s c.before) (tail : WriteChain c.packet.after cs t) : WriteChain s (c :: cs) t

def readBlocks : List ReadCall → Array Event
  | [] => #[]
  | c :: cs => c.packet.block ++ readBlocks cs

def writeBlocks : List WriteCall → Array Event
  | [] => #[]
  | c :: cs => c.packet.block ++ writeBlocks cs

/-- Exact ordered physical RAM folds, allowing arbitrary overlap between
calls. No PA-contiguity or fragment-disjointness condition is imposed. -/
def writeMemory (calls : List WriteCall) (mem : Std.ExtHashMap Nat (BitVec 8)) : Std.ExtHashMap Nat (BitVec 8) :=
  match calls with
  | [] => mem
  | c :: cs => writeMemory cs (wfold mem c.packet.ad.paddress.address.toNat c.request.bytes
      (fun j => (Sail.BitVec.castWidth (m := 8 * c.request.bytes) c.packet.data).extractLsb' (8 * j) 8))

theorem ReadChain.memory {s t : State} {cs : List ReadCall} (h : ReadChain s cs t) :
    t.mem = s.mem := by
  induction h with
  | nil f => exact f.2.1
  | cons c f tail ih => exact ih.trans (c.packet.memory.trans f.2.1)

theorem ReadChain.registers {s t : State} {cs : List ReadCall} (h : ReadChain s cs t) :
    t.regs = s.regs := by
  induction h with
  | nil f => exact f.1
  | cons c f tail ih => exact ih.trans (c.packet.registers.trans f.1)

theorem WriteChain.memory {s t : State} {cs : List WriteCall} (h : WriteChain s cs t) :
    t.mem = writeMemory cs s.mem := by
  induction h with
  | nil f => exact f.2.1
  | cons c f tail ih =>
    rw [ih,c.packet.memory,f.2.1]
    rfl

theorem WriteChain.registers {s t : State} {cs : List WriteCall} (h : WriteChain s cs t) :
    t.regs = s.regs := by
  induction h with
  | nil f => exact f.1
  | cons c f tail ih => exact ih.trans (c.packet.registers.trans f.1)

theorem ReadChain.events {s t : State} {cs : List ReadCall} (h : ReadChain s cs t) :
    t.events = s.events ++ readBlocks cs := by
  induction h with
  | nil f => simpa only [readBlocks,Array.append_empty] using f.2.2.1
  | cons c f tail ih =>
    rw [ih,c.packet.events_block,f.2.2.1,Array.append_assoc]
    rfl

theorem WriteChain.events {s t : State} {cs : List WriteCall} (h : WriteChain s cs t) :
    t.events = s.events ++ writeBlocks cs := by
  induction h with
  | nil f => simpa only [writeBlocks,Array.append_empty] using f.2.2.1
  | cons c f tail ih =>
    rw [ih,c.packet.events_block,f.2.2.1,Array.append_assoc]
    rfl

theorem ReadChain.choice {s t : State} {calls : List ReadCall} (chain : ReadChain s calls t) :
    ∃ draws, ChoiceDelta s t draws ∧ draws ≤ calls.length := by
  induction chain with
  | nil frame => exact ⟨0,frame.2.2.2,by simp⟩
  | cons call frame tail ih =>
    obtain ⟨draws,delta,bound⟩ := ih
    refine ⟨call.packet.draws + draws,?_,?_⟩
    · simpa only [Nat.zero_add] using
        choice_delta_trans (choice_delta_trans frame.2.2.2 call.packet.choice) delta
    · simp only [List.length_cons]
      have := call.packet.drawBound
      omega

theorem WriteChain.choice {s t : State} {calls : List WriteCall} (chain : WriteChain s calls t) :
    ∃ draws, ChoiceDelta s t draws ∧ draws ≤ calls.length := by
  induction chain with
  | nil frame => exact ⟨0,frame.2.2.2,by simp⟩
  | cons call frame tail ih =>
    obtain ⟨draws,delta,bound⟩ := ih
    refine ⟨call.packet.draws + draws,?_,?_⟩
    · simpa only [Nat.zero_add] using
        choice_delta_trans (choice_delta_trans frame.2.2.2 call.packet.choice) delta
    · simp only [List.length_cons]
      have := call.packet.drawBound
      omega

#print axioms ReadChain.memory
#print axioms ReadChain.registers
#print axioms WriteChain.memory
#print axioms WriteChain.registers
#print axioms ReadChain.events
#print axioms WriteChain.events
#print axioms ReadChain.choice
#print axioms WriteChain.choice
end TranslateSpan.DefaultAccessTrace
