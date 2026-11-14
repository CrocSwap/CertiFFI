import ArmCertLoop.CopyFacts
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false
namespace ArmCertLoop.SetNative
open ContractDraft

/-- Static fill deployment. Only actual destination byte writes are in the
data footprint; the initial contents of destination RAM are unconstrained. -/
structure Context where
  domain : QueryDomain
  spec : TopologyImageSpec domain
  config : AttributeConfig
  rows : List PermissionRow
  mapping : BitVec 64 → Option Nat
  base : BitVec 64
  d : BitVec 64
  fill : BitVec 64
  returnPC : BitVec 64
  n : Nat
  page : base.toNat % 4096 = 0
  low : base.toNat < 2 ^ 54
  returnLow : returnPC.toNat < 2 ^ 54
  destObject : SpanMap.NoWrap (destSpan d n)
  code : CodeGeometry mapping base
  codeWrite : CodeWriteSeparated mapping base d n
  data : ∀ i, i < n → ∃ pa : BitVec 56,
    mapping (d + BitVec.ofNat 64 i) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
    ¬ (rowsFootprint spec.imageRows).byte pa.toNat
  injective : SpanMap.UnionInjective mapping [destSpan d n]
  separated : ImageTableSeparated codeScope base mapping (rowsFootprint spec.imageRows).byte

def Context.spans (c : Context) : List SpanMap.Span := [destSpan c.d c.n]
def Context.consumer (c : Context) :=
  SpanMap.consumerMap c.spans (Image.codeVAs c.base Generated.imageStart Generated.imageWords)
    c.mapping (rowsFootprint c.spec.imageRows).byte
def Context.dstPA (c : Context) (i : Nat) : Nat := (c.mapping (c.d + BitVec.ofNat 64 i)).getD 0
def offset (c : Context) := Schedule.nativeOffset c.base c.returnPC (Schedule.setSteps c.n)
  (fun k => Generated.armcert_memset_entry + Schedule.setWordOffset c.n k)
abbrev Env (c : Context) (k : Nat) (x : NativeState) : Prop :=
  ArmCertPipe.ChainInvG c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.base
    (offset c) (Schedule.setSteps c.n) (fun _ _ => True) k x

structure Header (c : Context) (entry : NativeState) (i : Nat) (x : NativeState) : Prop where
  positive : 0 < c.n
  bound : i ≤ c.n
  environment : Env c (2 + 4 * i) x
  dest : x.regs.gpr[0] = c.d
  fill : x.regs.gpr[1] = c.fill
  cursor : x.regs.gpr[3] = c.d + BitVec.ofNat 64 i
  remaining : x.regs.gpr[2].toNat = c.n - i
  link : x.regs.gpr[30] = c.returnPC
  saved : ∀ r : Fin 31, 4 ≤ r.val → x.regs.gpr[r.val] = entry.regs.gpr[r.val]
  sp : x.regs.SP_EL0 = entry.regs.SP_EL0
  protectedRegs : NativeEntry.Effects.Frame {} entry.regs x.regs
  bytes : Bytes.FillPrefix c.dstPA (Aux.memoryView entry) (Aux.memoryView x) (c.fill.setWidth 8) c.n i

def Args (c : Context) (x : NativeState) : Prop :=
  x.regs.gpr[0] = c.d ∧ x.regs.gpr[1] = c.fill ∧ x.regs.gpr[2].toNat = c.n ∧ x.regs.gpr[30] = c.returnPC
def Post (c : Context) (entry fin : NativeState) : Prop :=
  fin.regs._PC = c.returnPC ∧ fin.regs.gpr[0] = c.d ∧
  (∀ i, i < c.n → readByte c.mapping fin (c.d + BitVec.ofNat 64 i) = some (c.fill.setWidth 8)) ∧
  (∀ pa, ¬ DestinationPA c.mapping c.d c.n pa → fin.mem[pa]? = entry.mem[pa]?) ∧
  (∀ r : Fin 31, 4 ≤ r.val → fin.regs.gpr[r.val] = entry.regs.gpr[r.val]) ∧
  fin.regs.SP_EL0 = entry.regs.SP_EL0 ∧ fin.regs._Z = entry.regs._Z ∧
  ArmFull.Register.FPCR.get fin.regs = ArmFull.Register.FPCR.get entry.regs ∧
  ArmFull.Register.FPSR.get fin.regs = ArmFull.Register.FPSR.get entry.regs

def fetch_index (c : Context) (k index : Nat) (x : NativeState) (env : Env c k x)
    (room : index < Generated.imageWords.length)
    (pc : x.regs._PC = MemReloc.imageAddress c.base (Generated.imageStart + 4 * index)) :
    FetchObligations c.spec c.config c.rows c.mapping (Generated.imageWords.getD index 0) x :=
  Image.fetch_word c.spec c.config c.rows c.mapping c.spans
    (rowsFootprint c.spec.imageRows).byte codeScope c.base Generated.imageStart Generated.imageWords
    (offset c) (Schedule.setSteps c.n) k index room x env.v2 pc
    (fun byte bounded => by unfold codeScope; have := room; simp only [Generated.imageWords_length, Generated.imageStart] at *; omega)
    (c.code index room).1 (c.code index room).2 c.separated

theorem body_room (c : Context) (i j : Nat) (room : i < c.n) (slot : j < 4) :
    2 + 4 * i + j < Schedule.setSteps c.n := by
  simp only [Schedule.setSteps, ite_eq_right (by omega : c.n ≠ 0)]
  omega

theorem offset_body (c : Context) (i j : Nat) (room : i < c.n) (slot : j < 4) :
    offset c (2 + 4 * i + j) = BitVec.ofNat 64 (464 + 4 * j) := by
  have index : 2 + 4 * i + j ≠ Schedule.setSteps c.n := Nat.ne_of_lt (body_room c i j room slot)
  simp only [offset, Schedule.nativeOffset, ite_eq_right index, Schedule.set_loop_offset c.n i j room slot,
    Generated.armcert_memset_entry]
  congr 1
  omega

theorem pc_body (c : Context) (i j : Nat) (room : i < c.n) (slot : j < 4) (x : NativeState)
    (env : Env c (2 + 4 * i + j) x) : x.regs._PC = MemReloc.imageAddress c.base (464 + 4 * j) := by
  rw [env.v2.v1.pc, offset_body c i j room slot]
  rfl

theorem body_aligned (c : Context) (i j : Nat) (room : i < c.n) (slot : j < 4) :
    (offset c (2 + 4 * i + j)).toNat % 4 = 0 := by
  rw [offset_body c i j room slot]
  have bound : 464 + 4 * j < 2 ^ 64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  omega

theorem body_next_placed (c : Context) (i j : Nat) (room : i < c.n) (slot : j < 3)
    (x : NativeState) (env : Env c (2 + 4 * i + j) x) :
    x.regs._PC + 4#64 = c.base + offset c (2 + 4 * i + j + 1) := by
  rw [pc_body c i j room (by omega) x env]
  have index : 2 + 4 * i + j + 1 = 2 + 4 * i + (j + 1) := by omega
  rw [index, offset_body c i (j + 1) room (by omega)]
  unfold MemReloc.imageAddress
  have word : 464 + 4 * (j + 1) = (464 + 4 * j) + 4 := by omega
  rw [word]
  simp only [BitVec.ofNat_add, BitVec.add_assoc]

theorem store_facts (c : Context) (i : Nat) (room : i < c.n) (x : NativeState)
    (cursor : x.regs.gpr[3] = c.d + BitVec.ofNat 64 i) :
    ArmCertMemPipe.StrbU.Facts c.spec c.mapping c.consumer (DestinationPA c.mapping c.d c.n) 0#12 3#5 x := by
  obtain ⟨pa, mapped, mmio, outside⟩ := c.data i room
  have addr : MemClass.StrbU.addr x 3#5 0#12 = c.d + BitVec.ofNat 64 i := by
    rw [CopyNative.store_addr_zero]; exact cursor
  refine ⟨pa, by rw [addr]; exact mapped, mmio, ?_, ?_, ?_⟩
  · intro j bounded
    have zero : j = 0 := by omega
    subst j
    simpa using outside
  · intro j bounded
    have zero : j = 0 := by omega
    subst j
    exact ⟨i, room, by simpa using mapped⟩
  · intro acc shape
    rw [addr]
    exact SpanMap.data_permitted c.spans (Image.codeVAs c.base Generated.imageStart Generated.imageWords)
      c.mapping (rowsFootprint c.spec.imageRows).byte (destSpan c.d c.n) (by simp [Context.spans]) i room acc shape

#print axioms fetch_index
#print axioms body_room
#print axioms offset_body
#print axioms pc_body
#print axioms body_aligned
#print axioms body_next_placed
#print axioms store_facts
end ArmCertLoop.SetNative
