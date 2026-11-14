import MemM1.M1CoreV
import MemM1.LeafFactsG
import M1a.PathWalk
import MemM1.M1CoreIF
import MemM1.LeafFactsGC
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
namespace MemM1.WalkFactV
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality S1OuterSetup ArmCert.Eval.JointSAT ArmCert.Eval.M1a MemM1.Witness MemM1.WitnessV

theorem ok_inj {α : Type} {a b : α} {s t : State}
    (h : (EStateM.Result.ok a s : EStateM.Result (Sail.Error exception) State α) = .ok b t) :
    a = b ∧ s = t := by
  cases h; exact ⟨rfl, rfl⟩

/-- Walk-side fact for one VA (eval's shape: j3b_translate_walk / walk_result_path): on every state
    with the registers and memory of `s`, the actual Get returns parameters satisfying Fields and
    Active, and on every such state the actual S1Walk with them returns the normal level-3 leaf
    result for the stored leaf descriptor `D`. -/
def WalkFact (s : State) (va : BitVec 64) (D : BitVec 64) : Prop :=
  ∀ t : State, t.regs = s.regs → t.mem = s.mem →
    ∀ (f : FaultRecord) (acc' : AccessDescriptor), f.statuscode = .Fault_None →
      acc'.ss = .SS_NonSecure →
      ∃ (wp : S1TTWParams) (u : State),
        AArch64_GetS1TTWParams .Regime_EL20 acc'.ss va t = .ok wp u ∧
        Frame t u ∧ EL20.Fields.Fields wp ∧ EL20.Active wp ∧
        ∀ v : State, v.regs = t.regs → v.mem = t.mem →
          ∃ (c : Context) (r : FaultRecord × AddressDescriptor × TTWState × BitVec 64)
            (w : State), c.wp = wp ∧ c.acc = acc' ∧ c.va = va ∧ c.regime = .Regime_EL20 ∧
            AArch64_S1Walk f wp va .Regime_EL20 acc' 64 v = .ok r w ∧ PostR c v D r w

/-- Raw-bit facts on a stored level-3 page descriptor (EL0 read/write data page). -/
structure LeafBits (D : BitVec 64) : Prop where
  idx : Sail.BitVec.extractLsb D 4 2 = 0#3 ∨ Sail.BitVec.extractLsb D 4 2 = 1#3
  ap : Sail.BitVec.extractLsb D 7 6 = 1#2
  af : D.getLsbD 10 = true
  dbm : D.getLsbD 51 = false
  dbm' : Sail.BitVec.access D 51 = 0#1
  cont : Sail.BitVec.access D 52 = 0#1

theorem walkOKV_of (s : State) (va D : BitVec 64) (hW : WalkFact s va D) (hD : LeafBits D)
    (acc : AccessDescriptor) (hA : Acc0 acc) :
    WalkOKV acc s va (MemM1.LeafFactsG.leafBase D) := by
  intro t htr htm
  let f0 : FaultRecord := { (default : FaultRecord) with statuscode := .Fault_None }
  rcases hW t htr htm f0 acc rfl hA.ss with ⟨wp, u, hg, hfr, hF, hAct, _⟩
  rcases hF with ⟨hee, hwxn, _, _, hpie, _, he0pd, _⟩
  rcases hAct with ⟨htg, hd128, haie, hds, hmair, htx, _⟩
  refine ⟨wp, u, hg, hfr, hd128, hpie, hds, htg, htx, hwxn, he0pd, ?_⟩
  intro f' v hf' hvr hvm
  rcases hW t htr htm f' acc hf' hA.ss with ⟨wp', u', hg', _, _, _, Hv⟩
  obtain rfl : wp' = wp := (ok_inj (hg'.symm.trans hg)).1
  rcases Hv v (hvr.trans htr.symm) (hvm.trans htm.symm) with
    ⟨c, ⟨fw, wa, w, d⟩, x, hcwp, _, _, _, hwalk, hwr, hwm, hd, hfw, _, cur, m, hcl, hcpas, hcapt, _, _, hlv⟩
  subst hcwp
  have hdec : S2FetchFrame.decoded c.wp.ee D = D := by
    unfold S2FetchFrame.decoded; rw [hee]; rfl
  rw [hdec] at hd hlv
  rcases MemM1.LeafFactsG.leafG_rw cur m c.wp D w v.regs hcl hcpas hmair hd128 htg hpie hds haie hcapt
      hD.idx hD.ap hD.dbm' hD.cont hlv with ⟨hmt, hap, hapt, hl, hc, hb, _⟩
  refine ⟨fw, wa, w, d, x, hwalk, hfw, hwr, hwm, ?_, ?_, hmt, hl, hc, hb, hap, hapt⟩
  · have hdD : d = D := hd
    rw [hdD]; exact hD.af
  · have hdD : d = D := hd
    rw [hdD]; exact hD.dbm

/-- Raw-bit facts on a stored level-3 CODE page descriptor (EL0 executable). -/
structure LeafBitsC (D : BitVec 64) : Prop where
  idx : Sail.BitVec.extractLsb D 4 2 = 0#3 ∨ Sail.BitVec.extractLsb D 4 2 = 1#3
  af : D.getLsbD 10 = true
  dbm : D.getLsbD 51 = false
  dbm' : Sail.BitVec.access D 51 = 0#1
  cont : Sail.BitVec.access D 52 = 0#1
  uxn : Sail.BitVec.access D 54 = 0#1
  gp : Sail.BitVec.access D 50 = 0#1

theorem walkOKIF_of (s : State) (va D : BitVec 64) (hW : WalkFact s va D) (hD : LeafBitsC D)
    (acc : AccessDescriptor) (hA : MemM1.WitnessIF.AccIF acc) :
    MemM1.WitnessIF.WalkOKIF acc s va (MemM1.LeafFactsG.leafBase D) := by
  intro t htr htm
  let f0 : FaultRecord := { (default : FaultRecord) with statuscode := .Fault_None }
  rcases hW t htr htm f0 acc rfl hA.ss with ⟨wp, u, hg, hfr, hF, hAct, _⟩
  rcases hF with ⟨hee, hwxn, _, _, hpie, _, he0pd, _⟩
  rcases hAct with ⟨htg, hd128, haie, hds, hmair, htx, _⟩
  refine ⟨wp, u, hg, hfr, hd128, hpie, hds, htg, htx, hwxn, he0pd, ?_⟩
  intro f' v hf' hvr hvm
  rcases hW t htr htm f' acc hf' hA.ss with ⟨wp', u', hg', _, _, _, Hv⟩
  obtain rfl : wp' = wp := (ok_inj (hg'.symm.trans hg)).1
  rcases Hv v (hvr.trans htr.symm) (hvm.trans htm.symm) with
    ⟨c, ⟨fw, wa, w, d⟩, x, hcwp, _, _, _, hwalk, hwr, hwm, hd, hfw, _, cur, m, hcl, hcpas, _, hcuxt, _, hlv⟩
  subst hcwp
  have hdec : S2FetchFrame.decoded c.wp.ee D = D := by
    unfold S2FetchFrame.decoded; rw [hee]; rfl
  rw [hdec] at hd hlv
  rcases MemM1.LeafFactsGC.leafGC_x cur m c.wp D w v.regs hcl hcpas hmair hd128 htg hpie hds haie hcuxt
      hD.idx hD.dbm' hD.cont hD.uxn hD.gp hlv with ⟨hmt, hl, hc, hb, hux, huxt, hgp⟩
  have hdD : d = D := hd
  refine ⟨fw, wa, w, d, x, hwalk, hfw, hwr, hwm, ?_, ?_, hmt, hl, hc, hb, hux, huxt, hgp⟩
  · rw [hdD]; exact hD.af
  · rw [hdD]; exact hD.dbm

#print axioms walkOKV_of
#print axioms walkOKIF_of
end MemM1.WalkFactV
