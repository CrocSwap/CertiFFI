import GetGuestFields.Region
import GetGuestFields.D128
import GetGuestFields.AIE
import GetGuestFields.PnCH
import GetGuestFields.ReadFields
import GetGuestFields.Preserves
import GetGuestFields.Total
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
set_option maxRecDepth 1000000
namespace GetGuestFields.Shape
open S1Normality

structure Raw (tcr tcr2 : BitVec 64) (s : State) : Prop where
  tcr_read : s.regs.bank_BitVec_64 .TCR_EL1 = tcr
  tcr2_read : s.regs.bank_BitVec_64 .TCR2_EL1 = tcr2
  mair_read : s.regs.bank_BitVec_64 .MAIR_EL1 = 0x000000040044ffff#64
  d128 : s.regs.FeatureImpl[178] = true → _get_TCR2_EL1_Type_D128 tcr2 = 0#1
  aie : s.regs.FeatureImpl[178] = true → _get_TCR2_EL1_Type_AIE tcr2 = 0#1
  pnch : s.regs.FeatureImpl[178] = true → _get_TCR2_EL1_Type_PnCH tcr2 = 0#1
  ds : _get_TCR_EL1_Type_DS tcr = 0#1

theorem Raw.frame {tcr tcr2 : BitVec 64} {s t : State} (h : Raw tcr tcr2 s)
    (hf : Frame s t) : Raw tcr tcr2 t := by
  exact ⟨by simpa only [hf.1] using h.tcr_read,
    by simpa only [hf.1] using h.tcr2_read,
    by simpa only [hf.1] using h.mair_read,
    by simpa only [hf.1] using h.d128,
    by simpa only [hf.1] using h.aie,
    by simpa only [hf.1] using h.pnch, h.ds⟩

def expected (tx : BitVec 6) (ps : BitVec 3) : ActiveView :=
  ⟨.TGx_4KB, 0#1, 0#1, 0#1, 0#1, 0x000000040044ffff#64, tx, ps⟩

theorem of_good (p : SailM S1TTWParams) (s : State) (v : ActiveView)
    (h : ReadFacts.Good s v (p s)) :
    ∃ wp t, p s = .ok wp t ∧ Frame s t ∧ active wp = v := by
  cases hr : p s with
  | error e t => simp only [hr, ReadFacts.Good] at h
  | ok wp t => exact ⟨wp, t, rfl, by simpa only [hr, ReadFacts.Good] using h⟩

private theorem frame_trans {s t u : State} (a : Frame s t) (b : Frame t u) : Frame s u :=
  ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.trans a.2.2⟩

theorem lower (tcr tcr2 : BitVec 64) (s : State) (raw : Raw tcr tcr2 s)
    (htg : _get_TCR_EL1_Type_TG0 tcr = 0#2) :
    ∃ wp t, AArch64_S1TTWParamsEL10 .VARange_LOWER s = .ok wp t ∧ Frame s t ∧
      active wp = expected (_get_TCR_EL1_Type_T0SZ tcr) (_get_TCR_EL1_Type_IPS tcr) := by
  rcases GetGuestFields.Normal.initial s with ⟨wp0, s0, h0, hf0⟩
  have good1 : ReadFacts.Good s0 {active wp0 with d128 := 0#1} (GetGuestFields.d128 wp0 s0) :=
    D128Facts.good wp0 tcr2 s0 (raw.frame hf0).tcr2_read (raw.frame hf0).d128
  rcases of_good (GetGuestFields.d128 wp0) s0 _ good1 with ⟨wp1, s1, h1, step1, hv1⟩
  have hf1 := frame_trans hf0 step1
  have good2 : ReadFacts.Good s1 {active wp1 with tgx := .TGx_4KB, txsz := _get_TCR_EL1_Type_T0SZ tcr} (GetGuestFields.region wp1 .VARange_LOWER s1) :=
    RegionFacts.lower wp1 tcr s1 (raw.frame hf1).tcr_read htg
  rcases of_good (GetGuestFields.region wp1 .VARange_LOWER) s1 _ good2 with ⟨wp2, s2, h2, step2, hv2⟩
  have hf2 := frame_trans hf1 step2
  have good3 : ReadFacts.Good s2 {active wp2 with mair := 0x000000040044ffff#64} (GetGuestFields.mair wp2 s2) :=
    ReadFacts.mair wp2 s2 (raw.frame hf2).mair_read
  rcases of_good (GetGuestFields.mair wp2) s2 _ good3 with ⟨wp3, s3, h3, step3, hv3⟩
  have hf3 := frame_trans hf2 step3
  rcases GetGuestFields.Preserves.mair2 wp3 s3 with ⟨wp4, s4, h4, step4, hv4⟩
  have hf4 := frame_trans hf3 step4
  have good5 : ReadFacts.Good s4 {active wp4 with aie := 0#1} (GetGuestFields.aie wp4 s4) :=
    AIEFacts.good wp4 tcr2 s4 (raw.frame hf4).tcr2_read (raw.frame hf4).aie
  rcases of_good (GetGuestFields.aie wp4) s4 _ good5 with ⟨wp5, s5, h5, step5, hv5⟩
  have hf5 := frame_trans hf4 step5
  rcases GetGuestFields.Preserves.wxn wp5 s5 with ⟨wp6, s6, h6, step6, hv6⟩
  have hf6 := frame_trans hf5 step6
  have good7 : ReadFacts.Good s6 {active wp6 with ps := _get_TCR_EL1_Type_IPS tcr} (GetGuestFields.ps wp6 s6) :=
    ReadFacts.ps wp6 tcr s6 (raw.frame hf6).tcr_read
  rcases of_good (GetGuestFields.ps wp6) s6 _ good7 with ⟨wp7, s7, h7, step7, hv7⟩
  have hf7 := frame_trans hf6 step7
  rcases GetGuestFields.Preserves.ee wp7 s7 with ⟨wp8, s8, h8, step8, hv8⟩
  have hf8 := frame_trans hf7 step8
  rcases GetGuestFields.Preserves.sif wp8 s8 with ⟨wp9, s9, h9, step9, hv9⟩
  have hf9 := frame_trans hf8 step9
  rcases GetGuestFields.Preserves.dc wp9 s9 with ⟨wp10, s10, h10, step10, hv10⟩
  have hf10 := frame_trans hf9 step10
  rcases GetGuestFields.Preserves.ntlsmd wp10 s10 with ⟨wp11, s11, h11, step11, hv11⟩
  have hf11 := frame_trans hf10 step11
  rcases GetGuestFields.Preserves.nv1 wp11 s11 with ⟨wp12, s12, h12, step12, hv12⟩
  have hf12 := frame_trans hf11 step12
  rcases GetGuestFields.Preserves.cmow wp12 s12 with ⟨wp13, s13, h13, step13, hv13⟩
  have hf13 := frame_trans hf12 step13
  rcases GetGuestFields.Preserves.ha wp13 s13 with ⟨wp14, s14, h14, step14, hv14⟩
  have hf14 := frame_trans hf13 step14
  rcases GetGuestFields.Preserves.hd wp14 s14 with ⟨wp15, s15, h15, step15, hv15⟩
  have hf15 := frame_trans hf14 step15
  have good16 : ReadFacts.Good s15 {active wp15 with ds := 0#1} (GetGuestFields.ds wp15 s15) :=
    ReadFacts.ds wp15 tcr s15 (raw.frame hf15).tcr_read (raw.frame hf15).ds
  rcases of_good (GetGuestFields.ds wp15) s15 _ good16 with ⟨wp16, s16, h16, step16, hv16⟩
  have hf16 := frame_trans hf15 step16
  rcases GetGuestFields.Preserves.pie wp16 s16 with ⟨wp17, s17, h17, step17, hv17⟩
  have hf17 := frame_trans hf16 step17
  rcases GetGuestFields.Preserves.pir wp17 s17 with ⟨wp18, s18, h18, step18, hv18⟩
  have hf18 := frame_trans hf17 step18
  rcases GetGuestFields.Preserves.epan wp18 s18 with ⟨wp19, s19, h19, step19, hv19⟩
  have hf19 := frame_trans hf18 step19
  have good20 : ReadFacts.Good s19 {active wp19 with pnch := 0#1} (GetGuestFields.pnch wp19 s19) :=
    PnCHFacts.good wp19 tcr2 s19 (raw.frame hf19).tcr2_read (raw.frame hf19).pnch
  rcases of_good (GetGuestFields.pnch wp19) s19 _ good20 with ⟨wp20, s20, h20, step20, hv20⟩
  have hf20 := frame_trans hf19 step20
  rcases GetGuestFields.Preserves.haft wp20 s20 with ⟨wp21, s21, h21, step21, hv21⟩
  have hf21 := frame_trans hf20 step21
  rcases GetGuestFields.Preserves.emec wp21 s21 with ⟨wp22, s22, h22, step22, hv22⟩
  have hf22 := frame_trans hf21 step22
  refine ⟨wp22, s22, ?_, hf22, ?_⟩
  · rw [GetGuestFields.source_eq]
    unfold GetGuestFields.composed
    rw [RegionFacts.bind_run h0, RegionFacts.bind_run h1, RegionFacts.bind_run h2, RegionFacts.bind_run h3, RegionFacts.bind_run h4, RegionFacts.bind_run h5, RegionFacts.bind_run h6, RegionFacts.bind_run h7, RegionFacts.bind_run h8, RegionFacts.bind_run h9, RegionFacts.bind_run h10, RegionFacts.bind_run h11, RegionFacts.bind_run h12, RegionFacts.bind_run h13, RegionFacts.bind_run h14, RegionFacts.bind_run h15, RegionFacts.bind_run h16, RegionFacts.bind_run h17, RegionFacts.bind_run h18, RegionFacts.bind_run h19, RegionFacts.bind_run h20, RegionFacts.bind_run h21, h22]
  · simp only [hv22, hv21, hv20, hv19, hv18, hv17, hv16, hv15, hv14, hv13, hv12, hv11, hv10, hv9, hv8, hv7, hv6, hv5, hv4, hv3, hv2, hv1, expected]
#print axioms lower

theorem upper (tcr tcr2 : BitVec 64) (s : State) (raw : Raw tcr tcr2 s)
    (htg : _get_TCR_EL1_Type_TG1 tcr = 2#2) :
    ∃ wp t, AArch64_S1TTWParamsEL10 .VARange_UPPER s = .ok wp t ∧ Frame s t ∧
      active wp = expected (_get_TCR_EL1_Type_T1SZ tcr) (_get_TCR_EL1_Type_IPS tcr) := by
  rcases GetGuestFields.Normal.initial s with ⟨wp0, s0, h0, hf0⟩
  have good1 : ReadFacts.Good s0 {active wp0 with d128 := 0#1} (GetGuestFields.d128 wp0 s0) :=
    D128Facts.good wp0 tcr2 s0 (raw.frame hf0).tcr2_read (raw.frame hf0).d128
  rcases of_good (GetGuestFields.d128 wp0) s0 _ good1 with ⟨wp1, s1, h1, step1, hv1⟩
  have hf1 := frame_trans hf0 step1
  have good2 : ReadFacts.Good s1 {active wp1 with tgx := .TGx_4KB, txsz := _get_TCR_EL1_Type_T1SZ tcr} (GetGuestFields.region wp1 .VARange_UPPER s1) :=
    RegionFacts.upper wp1 tcr s1 (raw.frame hf1).tcr_read htg
  rcases of_good (GetGuestFields.region wp1 .VARange_UPPER) s1 _ good2 with ⟨wp2, s2, h2, step2, hv2⟩
  have hf2 := frame_trans hf1 step2
  have good3 : ReadFacts.Good s2 {active wp2 with mair := 0x000000040044ffff#64} (GetGuestFields.mair wp2 s2) :=
    ReadFacts.mair wp2 s2 (raw.frame hf2).mair_read
  rcases of_good (GetGuestFields.mair wp2) s2 _ good3 with ⟨wp3, s3, h3, step3, hv3⟩
  have hf3 := frame_trans hf2 step3
  rcases GetGuestFields.Preserves.mair2 wp3 s3 with ⟨wp4, s4, h4, step4, hv4⟩
  have hf4 := frame_trans hf3 step4
  have good5 : ReadFacts.Good s4 {active wp4 with aie := 0#1} (GetGuestFields.aie wp4 s4) :=
    AIEFacts.good wp4 tcr2 s4 (raw.frame hf4).tcr2_read (raw.frame hf4).aie
  rcases of_good (GetGuestFields.aie wp4) s4 _ good5 with ⟨wp5, s5, h5, step5, hv5⟩
  have hf5 := frame_trans hf4 step5
  rcases GetGuestFields.Preserves.wxn wp5 s5 with ⟨wp6, s6, h6, step6, hv6⟩
  have hf6 := frame_trans hf5 step6
  have good7 : ReadFacts.Good s6 {active wp6 with ps := _get_TCR_EL1_Type_IPS tcr} (GetGuestFields.ps wp6 s6) :=
    ReadFacts.ps wp6 tcr s6 (raw.frame hf6).tcr_read
  rcases of_good (GetGuestFields.ps wp6) s6 _ good7 with ⟨wp7, s7, h7, step7, hv7⟩
  have hf7 := frame_trans hf6 step7
  rcases GetGuestFields.Preserves.ee wp7 s7 with ⟨wp8, s8, h8, step8, hv8⟩
  have hf8 := frame_trans hf7 step8
  rcases GetGuestFields.Preserves.sif wp8 s8 with ⟨wp9, s9, h9, step9, hv9⟩
  have hf9 := frame_trans hf8 step9
  rcases GetGuestFields.Preserves.dc wp9 s9 with ⟨wp10, s10, h10, step10, hv10⟩
  have hf10 := frame_trans hf9 step10
  rcases GetGuestFields.Preserves.ntlsmd wp10 s10 with ⟨wp11, s11, h11, step11, hv11⟩
  have hf11 := frame_trans hf10 step11
  rcases GetGuestFields.Preserves.nv1 wp11 s11 with ⟨wp12, s12, h12, step12, hv12⟩
  have hf12 := frame_trans hf11 step12
  rcases GetGuestFields.Preserves.cmow wp12 s12 with ⟨wp13, s13, h13, step13, hv13⟩
  have hf13 := frame_trans hf12 step13
  rcases GetGuestFields.Preserves.ha wp13 s13 with ⟨wp14, s14, h14, step14, hv14⟩
  have hf14 := frame_trans hf13 step14
  rcases GetGuestFields.Preserves.hd wp14 s14 with ⟨wp15, s15, h15, step15, hv15⟩
  have hf15 := frame_trans hf14 step15
  have good16 : ReadFacts.Good s15 {active wp15 with ds := 0#1} (GetGuestFields.ds wp15 s15) :=
    ReadFacts.ds wp15 tcr s15 (raw.frame hf15).tcr_read (raw.frame hf15).ds
  rcases of_good (GetGuestFields.ds wp15) s15 _ good16 with ⟨wp16, s16, h16, step16, hv16⟩
  have hf16 := frame_trans hf15 step16
  rcases GetGuestFields.Preserves.pie wp16 s16 with ⟨wp17, s17, h17, step17, hv17⟩
  have hf17 := frame_trans hf16 step17
  rcases GetGuestFields.Preserves.pir wp17 s17 with ⟨wp18, s18, h18, step18, hv18⟩
  have hf18 := frame_trans hf17 step18
  rcases GetGuestFields.Preserves.epan wp18 s18 with ⟨wp19, s19, h19, step19, hv19⟩
  have hf19 := frame_trans hf18 step19
  have good20 : ReadFacts.Good s19 {active wp19 with pnch := 0#1} (GetGuestFields.pnch wp19 s19) :=
    PnCHFacts.good wp19 tcr2 s19 (raw.frame hf19).tcr2_read (raw.frame hf19).pnch
  rcases of_good (GetGuestFields.pnch wp19) s19 _ good20 with ⟨wp20, s20, h20, step20, hv20⟩
  have hf20 := frame_trans hf19 step20
  rcases GetGuestFields.Preserves.haft wp20 s20 with ⟨wp21, s21, h21, step21, hv21⟩
  have hf21 := frame_trans hf20 step21
  rcases GetGuestFields.Preserves.emec wp21 s21 with ⟨wp22, s22, h22, step22, hv22⟩
  have hf22 := frame_trans hf21 step22
  refine ⟨wp22, s22, ?_, hf22, ?_⟩
  · rw [GetGuestFields.source_eq]
    unfold GetGuestFields.composed
    rw [RegionFacts.bind_run h0, RegionFacts.bind_run h1, RegionFacts.bind_run h2, RegionFacts.bind_run h3, RegionFacts.bind_run h4, RegionFacts.bind_run h5, RegionFacts.bind_run h6, RegionFacts.bind_run h7, RegionFacts.bind_run h8, RegionFacts.bind_run h9, RegionFacts.bind_run h10, RegionFacts.bind_run h11, RegionFacts.bind_run h12, RegionFacts.bind_run h13, RegionFacts.bind_run h14, RegionFacts.bind_run h15, RegionFacts.bind_run h16, RegionFacts.bind_run h17, RegionFacts.bind_run h18, RegionFacts.bind_run h19, RegionFacts.bind_run h20, RegionFacts.bind_run h21, h22]
  · simp only [hv22, hv21, hv20, hv19, hv18, hv17, hv16, hv15, hv14, hv13, hv12, hv11, hv10, hv9, hv8, hv7, hv6, hv5, hv4, hv3, hv2, hv1, expected]
#print axioms upper
end GetGuestFields.Shape
