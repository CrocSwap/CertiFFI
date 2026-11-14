-- Join of the actual __FetchInstr with canonical query invariant for the closed-run join:
-- from CurrentS1At/CurrentS1AccessAt at the ACTUAL beforeFetch state, the actual fetch returns the
-- actual post-walk word AND the invariant (CurrentS1At + the fetched query's CurrentS1AccessAt for
-- the SAME access data) holds on the actual post-fetch state. Reuses current_s1_after.
import ArmCertWalk.NativeFetchCurrent
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk
open ArmCert.Eval.M1a.Fetch2

theorem current_s1_frame {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {a b : State}
    (current : CurrentS1At spec config rows a) (registers : b.regs = a.regs) (memory : b.mem = a.mem) :
    CurrentS1At spec config rows b where
  images := current.images.frame registers memory
  host := host_walk_frame config spec.controls spec.physicalConfig a b current.host registers
  core := by rw [registers]; exact current.core
  geometry := by rw [registers]; exact current.geometry
  guards := by rw [registers]; exact current.guards
  rawFault := by rw [registers]; exact current.rawFault
  enabled := by rw [registers]; exact current.enabled
  cache := by rw [registers]; exact current.cache

theorem native_fetch_current_preserving {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : State) (step : StepFacts s.regs) (el : s.regs.PSTATE.EL = 0#2)
    (pcLow : Sail.BitVec.extractLsb s.regs._PC 1 0 = 0#2) (il : s.regs.PSTATE.IL = 0#1)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (queryOf : AccessDescriptor → AccessQuery)
    (rawOf : ∀ acc, (queryOf acc).request.raw = acc)
    (vaOf : ∀ acc, (queryOf acc).va = s.regs._PC)
    (mmio : MappedNotMMIO mapping s.regs._PC)
    (present : MappedBytesPresent mapping s.regs._PC s.mem)
    (perAcc : ∀ acc, ActualIFetchAcc s acc → domain (queryOf acc) ∧
      ∃ data : S1AccessData spec config rows (queryOf acc),
        CurrentS1AccessAt spec config rows mapping (queryOf acc) data s) :
    ∃ acc word final address faultOut translated,
      ∃ data : S1AccessData spec config rows (queryOf acc),
      ActualIFetchAcc s acc ∧
      __FetchInstr s.regs._PC s = .ok (__InstrEnc.__A64, word) final ∧
      CleanTranslateResultFields spec config rows mapping (queryOf acc) data.leafLevel data.view
        (fetchPre s) (faultOut, address) translated ∧
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? =
        some (word.extractLsb' (8 * i) 8)) ∧
      final.regs = translated.regs ∧ final.mem = translated.mem ∧
      final.events = translated.events.push
        (.memRead address.paddress.address.toNat 4 (some s.regs._PC.toNat) (AK_ifetch ()) false) ∧
      CurrentS1At spec config rows final ∧
      CurrentS1AccessAt spec config rows mapping (queryOf acc) data final := by
  have pre := current_s1_fetchPre current
  have modePre : HostEL0ModeAt (fetchPre s).regs := host_el0_mode_register_fields mode rfl rfl rfl rfl
  have debugPre : ExistingE11DebugAt (fetchPre s).regs := existing_e11_debug_register_fields debug rfl rfl
  have spePre : (fetchPre s).regs.bank_Bool .SPESampleInFlight = false :=
    (fetchRegs_bool_ne s.regs _ (by decide)).trans spe
  obtain ⟨acc, t, word, u, final, fetchCall, actual, tRegs, tMem, tEvents,
      ⟨address, faultOut, translated, data, clean, bytes, uEvents, uRegs, uMem, postCurrent, postAccess⟩,
      fRegs, fMem, fEvents⟩ :=
    fetch_frame_post s step pcLow il
      (fun acc t word u => ∃ address faultOut translated,
          ∃ data : S1AccessData spec config rows (queryOf acc),
        CleanTranslateResultFields spec config rows mapping (queryOf acc) data.leafLevel data.view
          (fetchPre s) (faultOut, address) translated ∧
        (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? =
          some (word.extractLsb' (8 * i) 8)) ∧
        u.events = translated.events.push
          (.memRead address.paddress.address.toNat 4 (some s.regs._PC.toNat) (AK_ifetch ()) false) ∧
        u.regs = translated.regs ∧ u.mem = translated.mem ∧
        CurrentS1At spec config rows translated ∧
        CurrentS1AccessAt spec config rows mapping (queryOf acc) data translated)
      (by
        intro t tRegs _ _
        obtain ⟨acc, after, call, _, frame⟩ :=
          MemM1.MemReadIF.createR t (by rw [tRegs]; exact step.rme) (by rw [tRegs]; exact step.nrw)
            (by rw [tRegs]; exact step.b3) (by rw [tRegs]; exact step.a3) (by rw [tRegs]; exact el)
            (by rw [tRegs]; exact step.ns)
        exact ⟨acc, after, call, frame⟩)
      (by
        intro acc actual t tRegs tMem _
        obtain ⟨t0, u0, t0Regs, t0Call⟩ := actual
        obtain ⟨acc0, after0, call0, shape0, _⟩ :=
          MemM1.MemReadIF.createR t0 (by rw [t0Regs]; exact step.rme) (by rw [t0Regs]; exact step.nrw)
            (by rw [t0Regs]; exact step.b3) (by rw [t0Regs]; exact step.a3) (by rw [t0Regs]; exact el)
            (by rw [t0Regs]; exact step.ns)
        have results := call0.symm.trans t0Call
        have same : acc0 = acc := by injection results
        subst same
        obtain ⟨member, data, access⟩ := perAcc acc0 ⟨t0, u0, t0Regs, t0Call⟩
        have va := vaOf acc0
        have raw := rawOf acc0
        have frameRegs : t.regs = (fetchPre s).regs := tRegs
        have frameMem : t.mem = (fetchPre s).mem := tMem
        have currentT := current_s1_frame pre frameRegs frameMem
        have accessP : CurrentS1AccessAt spec config rows mapping (queryOf acc0) data (fetchPre s) :=
          current_s1_access_registers access rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)
        have accessT : CurrentS1AccessAt spec config rows mapping (queryOf acc0) data t :=
          accessP.of_regs frameRegs
        obtain ⟨address, faultOut, translated, word, final, clean, bytes, readCall, events, regs, mem⟩ :=
          native_mem_read_total spec config rows mapping (queryOf acc0) member data.leafLevel data.logical
            data.physical data.view data.path data.permissions t data.lower currentT.host
            (by rw [frameRegs]; exact modePre) (by rw [frameRegs]; exact aa64)
            (by rw [frameRegs]; exact debugPre) (by rw [frameRegs]; exact spePre)
            currentT.core currentT.geometry accessT.layout currentT.images currentT.guards accessT.checks
            currentT.rawFault currentT.enabled data.accessEL data.nonsecure currentT.cache accessT.epd
            accessT.map accessT.outputPolicy (by rw [raw]; exact shape0)
            (by rw [va]; exact pc_low_aligned _ pcLow) (by rw [va]; exact mmio)
            (by rw [va, tMem]; exact present)
        have post := current_s1_after data currentT accessT (clean_translate_fields_to_clean clean)
        have cleanPre := clean_translate_result_memory_frames spec config rows mapping (queryOf acc0)
          data.leafLevel data.view (fetchPre s) t translated translated (faultOut, address)
          frameRegs frameMem rfl rfl clean
        have kept := clean
        obtain ⟨_, out, _, _, _, _, _, _, _, _, _, _, _, registers, _⟩ := kept
        refine ⟨word, final, ?_, ?_, address, faultOut, translated, data, cleanPre, bytes,
          by rw [events, va], regs, mem, post.1, post.2⟩
        · rw [va, raw] at readCall; exact readCall
        · rw [regs, registers]
          unfold fetchGuardRegs
          split <;> rfl)
  have finalRegs : final.regs = translated.regs := fRegs.trans uRegs
  have finalMem : final.mem = translated.mem := fMem.trans uMem
  exact ⟨acc, word, final, address, faultOut, translated, data, actual, fetchCall, clean, bytes,
    finalRegs, finalMem, fEvents.trans uEvents, current_s1_frame postCurrent finalRegs finalMem,
    postAccess.of_regs finalRegs⟩

#print axioms native_fetch_current_preserving
end ArmCertWalk
