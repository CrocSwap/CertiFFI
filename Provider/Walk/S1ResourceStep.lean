import Walk.S1OuterSetup
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
set_option maxRecDepth 1000000
namespace S1ResourceStep
open S1OuterSetup
abbrev Result := S1OuterStep.Result

def Next (c : Context) (mem : S1ResourcePath.Memory) (n : Nat) : Result → Prop
  | .error _ => True
  | .ok y => (stop y = true ∧ 1 ≤ (current y).level ∧ (current y).level ≤ 3) ∨
      (stop y = false ∧ ∃ m : Nat, m < n ∧
      S1ResourcePath.Slots c.wp c.va mem m (current y).level (slot y))

theorem total (c : Context) (x : Vars) (s : State) (n : Nat)
    (hReady : Ready c s) (hFault : (fault x).statuscode = .Fault_None)
    (hPAS : (current x).baseaddress.paspace = .PAS_NonSecure)
    (hPath : S1ResourcePath.Slots c.wp c.va s.mem n (current x).level (slot x)) :
    ∃ (result : Result) (t : State),
      S1WalkSource.named.body0 c.wp c.va c.regime c.acc 64 c.startlevel x s = .ok result t ∧
      S1OuterStep.Progress (current x) (fault x) result ∧ t.regs = s.regs ∧
      S1MemoryObservation.Equivalent (S1TableUpdate10.observe c.wp) s.mem t.mem ∧
      Next c t.mem n result := by
  rcases x with ⟨aligned, descaddr, d, typ, f, a64, s2fs1mro, skl, walkaddr, w⟩
  change f.statuscode = .Fault_None at hFault
  change w.baseaddress.paspace = .PAS_NonSecure at hPAS
  change S1ResourcePath.Slots c.wp c.va s.mem n w.level descaddr at hPath
  rcases S1ResourcePath.unroll hPath with ⟨canonical, hBounds, hRAM, hAlign, hObserved, hBranch⟩
  rcases hObserved with ⟨raw, hBytes, hView⟩
  have hStable := S1ResourcePath.observed_stable c.wp raw canonical hView
  have hClass := S1StablePath.classify_eq (S2FetchFrame.decoded c.wp.ee raw) canonical w.level hStable
  rcases S1OuterStep.total c.regime c.regimes c.wp c.va c.acc c.startlevel
    aligned descaddr d typ f a64 s2fs1mro skl walkaddr w c.cfg raw s
    c.d128 c.ds c.tg c.aie c.mair hBounds hPAS hReady.pa hFault hReady.config
    c.vm c.dc c.ss hReady.el hReady.noRME hReady.a64 hReady.el3A64 hReady.noEL3A32
    hRAM hAlign hBytes with ⟨result, t, hrun, hProgress, hDetailed, hRegs, hObs⟩
  refine ⟨result, t, hrun, hProgress, hRegs, hObs, ?_⟩
  cases result with
  | error e => trivial
  | ok y =>
    rcases y with ⟨ao, addr, out, ty, fo, a64o, mro, sklo, wa, next⟩
    rcases hDetailed with ⟨hleaf, hLeafClass, hLeafShape⟩ | ⟨htable, hDecode, hAddr, hRange, hShape⟩
    · subst ty
      refine Or.inl ⟨rfl, ?_⟩
      change 1 ≤ next.level ∧ next.level ≤ 3
      have hLevels := S1LeafShape.leaf_levels _ _ hLeafClass
      rw [hLeafShape.2.1]
      omega

    · have hTable : S1DecodeFacts.classify canonical w.level = .DescriptorType_Table :=
        hClass.symm.trans hDecode
      have hSlot : addr = S1ResourcePath.nextSlot c.va w.level canonical :=
        hAddr.trans ((S1ResourcePath.next_of_shape c.va (S2FetchFrame.decoded c.wp.ee raw) w next hShape).trans
          (S1ResourcePath.next_stable c.va w.level _ canonical hStable))
      cases hBranch with
      | terminal hStop => exact False.elim (hStop hTable)
      | tableFault _ hBad =>
        rw [hSlot] at hRange
        rw [hBad] at hRange
        contradiction
      | @table m level word _ _ rest =>
        have hRest := S1ResourcePath.transport rest hObs
        refine Or.inr ⟨?_, m, by omega, ?_⟩
        · change (ty == .DescriptorType_Leaf) = false
          rw [htable]
          rfl

        · change S1ResourcePath.Slots c.wp c.va t.mem m next.level addr
          rw [hShape.2.1, hSlot]
          exact hRest
#print axioms total
end S1ResourceStep
