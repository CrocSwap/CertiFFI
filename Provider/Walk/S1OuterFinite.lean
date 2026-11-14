import Walk.S1ResourceStep
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
set_option maxRecDepth 1000000
namespace S1OuterFinite
open S1OuterSetup
abbrev Result := S1OuterStep.Result

theorem successor_ready (w : TTWState) (f : FaultRecord) (y : Vars)
    (h : S1OuterStep.Progress w f (.ok y)) (hf : f.statuscode = .Fault_None) :
    (fault y).statuscode = .Fault_None ∧
    (current y).baseaddress.paspace = .PAS_NonSecure := by
  rcases y with ⟨a, addr, d, typ, fo, a64, mro, skl, wa, next⟩
  rcases h with ⟨hfo, ⟨_, _, hp⟩ | ⟨_, _, hp⟩⟩ <;>
    exact ⟨by simpa only [fault, hfo] using hf, hp⟩

theorem observation_trans {wp : S1TTWParams} {m1 m2 m3 : S1ResourcePath.Memory}
    (h1 : S1MemoryObservation.Equivalent (S1TableUpdate10.observe wp) m1 m2)
    (h2 : S1MemoryObservation.Equivalent (S1TableUpdate10.observe wp) m2 m3) :
    S1MemoryObservation.Equivalent (S1TableUpdate10.observe wp) m1 m3 := by
  intro a ha v
  exact (h1 a ha v).trans (h2 a ha v)

def Endpoint : Result → Prop
  | .error (.inl _) => False
  | .error (.inr _) => True
  | .ok y => stop y = true ∧ 1 ≤ (current y).level ∧ (current y).level ≤ 3

theorem trace (c : Context) (n : Nat) (x : Vars) (s : State)
    (hReady : Ready c s) (hFault : (fault x).statuscode = .Fault_None)
    (hPAS : (current x).baseaddress.paspace = .PAS_NonSecure)
    (hPath : S1ResourcePath.Slots c.wp c.va s.mem n (current x).level (slot x)) :
    ∃ (steps : Nat) (result : Result) (t : State), 0 < steps ∧ steps ≤ n ∧
      S2Loop.Trace stop (S1WalkSource.named.body0 c.wp c.va c.regime c.acc 64 c.startlevel)
        steps x s result t ∧ Endpoint result ∧ t.regs = s.regs ∧
      S1MemoryObservation.Equivalent (S1TableUpdate10.observe c.wp) s.mem t.mem := by
  induction n using Nat.strongRecOn generalizing x s with
  | ind n ih =>
    have hn : 0 < n := (S1ResourcePath.length_bound hPath).1
    rcases S1ResourceStep.total c x s n hReady hFault hPAS hPath with
      ⟨result, t, hrun, hProgress, hRegs, hObs, hNext⟩
    cases result with
    | error e =>
      cases e with
      | inl err => exact False.elim hProgress
      | inr r => exact ⟨1, .error (.inr r), t, by omega, by omega, .returned hrun, by trivial, hRegs, hObs⟩
    | ok y =>
      change (stop y = true ∧ 1 ≤ (current y).level ∧ (current y).level ≤ 3) ∨
        (stop y = false ∧ ∃ m, m < n ∧
          S1ResourcePath.Slots c.wp c.va t.mem m (current y).level (slot y)) at hNext
      rcases hNext with ⟨hStop, hLevels⟩ | ⟨hStop, m, hm, hRest⟩
      · exact ⟨1, .ok y, t, by omega, by omega, .done hrun hStop,
          ⟨hStop, hLevels⟩, hRegs, hObs⟩
      · have hReadyNext := Ready.of_regs hReady hRegs
        have hNextState := successor_ready (current x) (fault x) y hProgress hFault
        rcases ih m hm y t hReadyNext hNextState.1 hNextState.2 hRest with
          ⟨steps, result, u, hPositive, hBound, hTrace, hEnd, hRegs2, hObs2⟩
        exact ⟨steps + 1, result, u, by omega, by omega, .next hrun hStop hTrace,
          hEnd, hRegs2.trans hRegs, observation_trans hObs hObs2⟩

theorem loop_total (c : Context) (aligned : Bool) (descaddr : FullAddress)
    (d : BitVec 64) (typ : DescriptorType) (f : FaultRecord) (a64 mro : Bool)
    (skl : BitVec 2) (walkaddr : AddressDescriptor) (w : TTWState) (s : State) (n : Nat)
    (hReady : Ready c s) (hFault : f.statuscode = .Fault_None)
    (hPAS : w.baseaddress.paspace = .PAS_NonSecure)
    (hPath : S1ResourcePath.Slots c.wp c.va s.mem n w.level descaddr) :
    ∃ (steps : Nat) (result : Result) (t : State),
      0 < steps ∧ steps ≤ (4 - w.level).toNat ∧
      S1WalkSource.named.loop0 c.wp c.va c.regime c.acc 64 a64 aligned f w c.startlevel
        d skl walkaddr mro typ descaddr s = .ok result t ∧ Endpoint result ∧ t.regs = s.regs ∧
      S1MemoryObservation.Equivalent (S1TableUpdate10.observe c.wp) s.mem t.mem := by
  rcases trace c n (aligned, descaddr, d, typ, f, a64, mro, skl, walkaddr, w) s
    hReady hFault hPAS hPath with ⟨steps, result, t, hPositive, hBound, hTrace, hEnd, hRegs, hObs⟩
  have hLength := S1ResourcePath.length_bound hPath
  have hLevel := S1ResourcePath.unroll hPath
  rcases hLevel with ⟨_, hLevel, _⟩
  have hEnough : steps ≤ 1048576 := by omega
  refine ⟨steps, result, t, hPositive, Nat.le_trans hBound hLength.2, ?_, hEnd, hRegs, hObs⟩
  simpa only [S1WalkSource.named.loop0, stop] using S2Loop.execute hTrace 1048576 hEnough
#print axioms trace
#print axioms loop_total
end S1OuterFinite
