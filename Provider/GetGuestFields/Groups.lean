import GetGuestComposition.Params
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace GetGuestFields
/- Exact stages of the gated compositional native. Each stage takes an abstract
   input record, so field facts never expand earlier record/state histories. -/

noncomputable def initial : SailM S1TTWParams := do
  let walkparams ← (( do (S1ParamsUnknown.native (← GetGuestReads.occurrence 1260)) ) : SailM S1TTWParams )
  pure walkparams

noncomputable def d128 (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__2 ← (( do
    if ((← do
         (GetGuestFeatures.Have128BitDescriptorExt.native)) : Bool)
    then
      (do
        (GetGuestTCR2.native))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__2 : Bool)
    then
      (do
        let w__3 ← (( do GetGuestReads.read TCR2_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with d128 := (_get_TCR2_EL1_Type_D128 w__3) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with d128 := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  pure walkparams

noncomputable def region (walkparams : S1TTWParams) (varange : VARange) : SailM S1TTWParams := do
  let walkparams ← (( do
    if ((BEq.beq varange .VARange_LOWER) : Bool)
    then
      (do
        let w__4 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
        let w__5 ← (( do (GetGuestVirtualization.TG0.native (_get_TCR_EL1_Type_TG0 w__4)) ) : SailM TGx )
        let walkparams := ({ walkparams with tgx := w__5 } : S1TTWParams)
        let w__6 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with txsz := (_get_TCR_EL1_Type_T0SZ w__6) } : S1TTWParams)
        let w__7 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with irgn := (_get_TCR_EL1_Type_IRGN0 w__7) } : S1TTWParams)
        let w__8 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with orgn := (_get_TCR_EL1_Type_ORGN0 w__8) } : S1TTWParams)
        let w__9 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with sh := (_get_TCR_EL1_Type_SH0 w__9) } : S1TTWParams)
        let w__10 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with tbi := (_get_TCR_EL1_Type_TBI0 w__10) } : S1TTWParams)
        let w__13 ← (( do
          if ((← do
               (GetGuestFeatures.HaveSVE.native)) : Bool)
          then (pure true)
          else
            (do
              (GetGuestFeatures.HaveTME.native)) ) : SailM Bool )
        let w__15 ← (( do
          if (w__13 : Bool)
          then
            (do
              let w__14 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_NFD0 w__14))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with nfd := w__15 } : S1TTWParams)
        let w__16 ← (( do (GetGuestFeatures.HavePACExt.native) ) : SailM Bool )
        let w__18 ← (( do
          if (w__16 : Bool)
          then
            (do
              let w__17 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_TBID0 w__17))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with tbid := w__18 } : S1TTWParams)
        let w__19 ← (( do (GetGuestFeatures.HaveE0PDExt.native) ) : SailM Bool )
        let w__21 ← (( do
          if (w__19 : Bool)
          then
            (do
              let w__20 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_E0PD0 w__20))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with e0pd := w__21 } : S1TTWParams)
        let w__22 ← (( do (GetGuestFeatures.AArch64_HaveHPDExt.native) ) : SailM Bool )
        let w__24 ← (( do
          if (w__22 : Bool)
          then
            (do
              let w__23 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_HPD0 w__23))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with hpd := w__24 } : S1TTWParams)
        let w__25 ← (( do (GetGuestFeatures.HaveMTE4Ext.native) ) : SailM Bool )
        let w__27 ← (( do
          if (w__25 : Bool)
          then
            (do
              let w__26 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_MTX0 w__26))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with mtx := w__27 } : S1TTWParams)
        let w__29 ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              let w__28 ← (( do (GetGuestVirtualization.TTBR0.native) ) : SailM (BitVec 128) )
              (pure ((_get_TTBR0_EL1_Type_SKL w__28))))
          else (pure (0b00#2)) ) : SailM (BitVec 2) )
        let walkparams := ({ walkparams with skl := w__29 } : S1TTWParams)
        let w__31 ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              let w__30 ← (( do GetGuestReads.read TCR2_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR2_EL1_Type_DisCH0 w__30))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with disch := w__31 } : S1TTWParams)
        (pure (walkparams)))
    else
      (do
        let w__32 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
        let w__33 ← (( do (GetGuestVirtualization.TG1.native (_get_TCR_EL1_Type_TG1 w__32)) ) : SailM TGx )
        let walkparams := ({ walkparams with tgx := w__33 } : S1TTWParams)
        let w__34 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with txsz := (_get_TCR_EL1_Type_T1SZ w__34) } : S1TTWParams)
        let w__35 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with irgn := (_get_TCR_EL1_Type_IRGN1 w__35) } : S1TTWParams)
        let w__36 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with orgn := (_get_TCR_EL1_Type_ORGN1 w__36) } : S1TTWParams)
        let w__37 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with sh := (_get_TCR_EL1_Type_SH1 w__37) } : S1TTWParams)
        let w__38 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with tbi := (_get_TCR_EL1_Type_TBI1 w__38) } : S1TTWParams)
        let w__41 ← (( do
          if ((← do
               (GetGuestFeatures.HaveSVE.native)) : Bool)
          then (pure true)
          else
            (do
              (GetGuestFeatures.HaveTME.native)) ) : SailM Bool )
        let w__43 ← (( do
          if (w__41 : Bool)
          then
            (do
              let w__42 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_NFD1 w__42))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with nfd := w__43 } : S1TTWParams)
        let w__44 ← (( do (GetGuestFeatures.HavePACExt.native) ) : SailM Bool )
        let w__46 ← (( do
          if (w__44 : Bool)
          then
            (do
              let w__45 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_TBID1 w__45))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with tbid := w__46 } : S1TTWParams)
        let w__47 ← (( do (GetGuestFeatures.HaveE0PDExt.native) ) : SailM Bool )
        let w__49 ← (( do
          if (w__47 : Bool)
          then
            (do
              let w__48 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_E0PD1 w__48))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with e0pd := w__49 } : S1TTWParams)
        let w__50 ← (( do (GetGuestFeatures.AArch64_HaveHPDExt.native) ) : SailM Bool )
        let w__52 ← (( do
          if (w__50 : Bool)
          then
            (do
              let w__51 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_HPD1 w__51))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with hpd := w__52 } : S1TTWParams)
        let w__53 ← (( do (GetGuestFeatures.HaveMTE4Ext.native) ) : SailM Bool )
        let w__55 ← (( do
          if (w__53 : Bool)
          then
            (do
              let w__54 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_MTX1 w__54))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with mtx := w__55 } : S1TTWParams)
        let w__57 ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              let w__56 ← (( do (GetGuestVirtualization.TTBR1.native) ) : SailM (BitVec 128) )
              (pure ((_get_TTBR1_EL1_Type_SKL w__56))))
          else (pure (0b00#2)) ) : SailM (BitVec 2) )
        let walkparams := ({ walkparams with skl := w__57 } : S1TTWParams)
        let w__59 ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              let w__58 ← (( do GetGuestReads.read TCR2_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR2_EL1_Type_DisCH1 w__58))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with disch := w__59 } : S1TTWParams)
        (pure (walkparams))) ) : SailM S1TTWParams )
  pure walkparams

noncomputable def mair (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__60 ← (( do GetGuestReads.read MAIR_EL1 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with mair := (Mk_MAIRType w__60) } : S1TTWParams)
  pure walkparams

noncomputable def mair2 (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__61 ← (( do (GetGuestFeatures.HaveAIEExt.native) ) : SailM Bool )
  let walkparams ← (( do
    if (w__61 : Bool)
    then
      (do
        let w__62 ← (( do GetGuestReads.read MAIR2_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with mair2 := (Mk_MAIRType w__62) } : S1TTWParams)
        (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  pure walkparams

noncomputable def aie (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__65 ← (( do
    if ((← do
         (GetGuestFeatures.HaveAIEExt.native)) : Bool)
    then
      (do
        (GetGuestTCR2.native))
    else (pure false) ) : SailM Bool )
  let w__67 ← (( do
    if (w__65 : Bool)
    then
      (do
        let w__66 ← (( do GetGuestReads.read TCR2_EL1 ) : SailM (BitVec 64) )
        (pure ((_get_TCR2_EL1_Type_AIE w__66))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with aie := w__67 } : S1TTWParams)
  pure walkparams

noncomputable def wxn (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__68 ← (( do GetGuestReads.read SCTLR_EL1 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with wxn := (_get_SCTLR_EL1_Type_WXN w__68) } : S1TTWParams)
  pure walkparams

noncomputable def ps (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__69 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ps := (_get_TCR_EL1_Type_IPS w__69) } : S1TTWParams)
  pure walkparams

noncomputable def ee (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__70 ← (( do GetGuestReads.read SCTLR_EL1 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ee := (_get_SCTLR_EL1_Type_EE w__70) } : S1TTWParams)
  pure walkparams

noncomputable def sif (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__74 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        if ((← do
             let w__71 ← (( do (GetGuestFeatures.HaveRME.native) ) : SailM Bool )
             (pure (((! w__71) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            (GetGuestFeatures.HaveSecureEL2Ext.native)))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__74 : Bool)
    then
      (do
        let w__75 ← (( do GetGuestReads.read SCR_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with sif := (_get_SCR_EL3_Type_SIF w__75) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with sif := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  pure walkparams

noncomputable def dc (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__76 ← (( do (S1EL2Enabled.native) ) : SailM Bool )
  let walkparams ← (( do
    if (w__76 : Bool)
    then
      (do
        let w__77 ← (( do GetGuestReads.read HCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with dc := (_get_HCR_EL2_Type_DC w__77) } : S1TTWParams)
        let w__78 ← (( do (GetGuestFeatures.HaveMTE2Ext.native) ) : SailM Bool )
        let w__80 ← (( do
          if (w__78 : Bool)
          then
            (do
              let w__79 ← (( do GetGuestReads.read HCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_HCR_EL2_Type_DCT w__79))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with dct := w__80 } : S1TTWParams)
        (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  pure walkparams

noncomputable def ntlsmd (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__81 ← (( do (GetGuestFeatures.HaveTrapLoadStoreMultipleDeviceExt.native) ) : SailM Bool )
  let walkparams ← (( do
    if (w__81 : Bool)
    then
      (do
        let w__82 ← (( do GetGuestReads.read SCTLR_EL1 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with ntlsmd := (_get_SCTLR_EL1_Type_nTLSMD w__82) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with ntlsmd := 1#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  pure walkparams

noncomputable def nv1 (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__83 ← (( do (S1EL2Enabled.native) ) : SailM Bool )
  let walkparams ← (( do
    if (w__83 : Bool)
    then
      (do
        let w__84 ← (( do GetGuestReads.read HCR_EL2 ) : SailM (BitVec 64) )
        let w__85 ← (( do GetGuestReads.read HCR_EL2 ) : SailM (BitVec 64) )
        if ((((_get_HCR_EL2_Type_NV w__84) +++ (_get_HCR_EL2_Type_NV1 w__85)) == 0b01#2) : Bool)
        then
          (do
            let w__86 ← (( do (GetGuestVirtualization.Constraint.native) ) : SailM Constraint )
            let walkparams : S1TTWParams :=
              match w__86 with
              | .Constraint_NVNV1_00 => { walkparams with nv1 := 0#1 }
              | .Constraint_NVNV1_01 => { walkparams with nv1 := 1#1 }
              | .Constraint_NVNV1_11 => { walkparams with nv1 := 1#1 }
              | _ => walkparams
            (pure (walkparams)))
        else
          (do
            let w__87 ← (( do GetGuestReads.read HCR_EL2 ) : SailM (BitVec 64) )
            let walkparams :=
              ({ walkparams with nv1 := (_get_HCR_EL2_Type_NV1 w__87) } : S1TTWParams)
            (pure (walkparams))))
    else
      (let walkparams : S1TTWParams := { walkparams with nv1 := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  pure walkparams

noncomputable def cmow (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__88 ← (( do (GetGuestFeatures.HaveFeatCMOW.native) ) : SailM Bool )
  let w__90 ← (( do
    if (w__88 : Bool)
    then
      (do
        let w__89 ← (( do GetGuestReads.read SCTLR_EL1 ) : SailM (BitVec 64) )
        (pure ((_get_SCTLR_EL1_Type_CMOW w__89))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with cmow := w__90 } : S1TTWParams)
  pure walkparams

noncomputable def ha (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__91 ← (( do (GetGuestFeatures.HaveAccessFlagUpdateExt.native) ) : SailM Bool )
  let w__93 ← (( do
    if (w__91 : Bool)
    then
      (do
        let w__92 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL1_Type_HA w__92))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ha := w__93 } : S1TTWParams)
  pure walkparams

noncomputable def hd (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__94 ← (( do (GetGuestFeatures.HaveDirtyBitModifierExt.native) ) : SailM Bool )
  let w__96 ← (( do
    if (w__94 : Bool)
    then
      (do
        let w__95 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL1_Type_HD w__95))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hd := w__96 } : S1TTWParams)
  pure walkparams

noncomputable def ds (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__98 ← (( do
    if ((((BEq.beq walkparams.tgx .TGx_4KB) || (BEq.beq walkparams.tgx .TGx_16KB)) : Bool) : Bool)
    then
      (do
        (GetGuestFeatures.Have52BitIPAAndPASpaceExt.native))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__98 : Bool)
    then
      (do
        let w__99 ← (( do GetGuestReads.read TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with ds := (_get_TCR_EL1_Type_DS w__99) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with ds := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  pure walkparams

noncomputable def pie (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let walkparams ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (let walkparams : S1TTWParams := { walkparams with pie := 1#1 }
      (pure (walkparams)))
    else
      (do
        let w__102 ← (( do
          if ((← do
               (GetGuestFeatures.HaveS1PIExt.native)) : Bool)
          then
            (do
              (GetGuestTCR2.native))
          else (pure false) ) : SailM Bool )
        let w__104 ← (( do
          if (w__102 : Bool)
          then
            (do
              let w__103 ← (( do GetGuestReads.read TCR2_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR2_EL1_Type_PIE w__103))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with pie := w__104 } : S1TTWParams)
        (pure (walkparams))) ) : SailM S1TTWParams )
  pure walkparams

noncomputable def pir (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__105 ← (( do (GetGuestFeatures.HaveS1PIExt.native) ) : SailM Bool )
  let walkparams ← (( do
    if (w__105 : Bool)
    then
      (do
        let w__106 ← (( do GetGuestReads.read PIR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with pir := (Mk_S1PIRType w__106) } : S1TTWParams)
        if ((walkparams.nv1 != 1#1) : Bool)
        then
          (do
            let w__107 ← (( do GetGuestReads.read PIRE0_EL1 ) : SailM (BitVec 64) )
            let walkparams := ({ walkparams with pire0 := (Mk_S1PIRType w__107) } : S1TTWParams)
            (pure (walkparams)))
        else (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  pure walkparams

noncomputable def epan (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__108 ← (( do (GetGuestFeatures.HavePAN3Ext.native) ) : SailM Bool )
  let walkparams ← (( do
    if (w__108 : Bool)
    then
      (do
        let w__110 ← (( do
          if ((walkparams.pie == 0#1) : Bool)
          then
            (do
              let w__109 ← (( do GetGuestReads.read SCTLR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL1_Type_EPAN w__109))))
          else (pure (1#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with epan := w__110 } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with epan := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  pure walkparams

noncomputable def pnch (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__114 ← (( do
    if ((← do
         (pure ((← do
               (GetGuestFeatures.HaveTHExt.native)) && ((walkparams.d128 == 0#1) : Bool)))) : Bool)
    then
      (do
        (GetGuestTCR2.native))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__114 : Bool)
    then
      (do
        let w__115 ← (( do GetGuestReads.read TCR2_EL1 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with pnch := (_get_TCR2_EL1_Type_PnCH w__115) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with pnch := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  pure walkparams

noncomputable def haft (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__119 ← (( do
    if ((← do
         (pure ((← do
               (GetGuestFeatures.HaveAccessFlagUpdateForTableExt.native)) && ((walkparams.ha == 1#1) : Bool)))) : Bool)
    then
      (do
        (GetGuestTCR2.native))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__119 : Bool)
    then
      (do
        let w__120 ← (( do GetGuestReads.read TCR2_EL1 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with haft := (_get_TCR2_EL1_Type_HAFT w__120) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with haft := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  pure walkparams

noncomputable def emec (walkparams : S1TTWParams) : SailM S1TTWParams := do
  let w__123 ← (( do
    if ((← do
         (GetGuestFeatures.HaveFeatMEC.native)) : Bool)
    then
      (do
        (GetGuestSCTLR2.native))
    else (pure false) ) : SailM Bool )
  let w__125 ← (( do
    if (w__123 : Bool)
    then
      (do
        let w__124 ← (( do GetGuestReads.read SCTLR2_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_SCTLR2_EL2_Type_EMEC w__124))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with emec := w__125 } : S1TTWParams)
  pure walkparams

noncomputable def composed (varange : VARange) : SailM S1TTWParams := do
  let walkparams ← initial
  let walkparams ← d128 walkparams
  let walkparams ← region walkparams varange
  let walkparams ← mair walkparams
  let walkparams ← mair2 walkparams
  let walkparams ← aie walkparams
  let walkparams ← wxn walkparams
  let walkparams ← ps walkparams
  let walkparams ← ee walkparams
  let walkparams ← sif walkparams
  let walkparams ← dc walkparams
  let walkparams ← ntlsmd walkparams
  let walkparams ← nv1 walkparams
  let walkparams ← cmow walkparams
  let walkparams ← ha walkparams
  let walkparams ← hd walkparams
  let walkparams ← ds walkparams
  let walkparams ← pie walkparams
  let walkparams ← pir walkparams
  let walkparams ← epan walkparams
  let walkparams ← pnch walkparams
  let walkparams ← haft walkparams
  let walkparams ← emec walkparams
  pure walkparams

theorem state_bind_assoc {ε σ α β γ : Type} (p : σ → EStateM.Result ε σ α)
    (f : α → σ → EStateM.Result ε σ β) (g : β → σ → EStateM.Result ε σ γ) :
    EStateM.bind (EStateM.bind p f) g = EStateM.bind p (fun a => EStateM.bind (f a) g) := by
  funext s
  cases h : p s <;> simp [EStateM.bind, h]

theorem state_pure_bind {ε σ α β : Type} (a : α) (f : α → σ → EStateM.Result ε σ β) :
    EStateM.bind (EStateM.pure a) f = f a := rfl

theorem state_bind_pure {ε σ α : Type} (p : σ → EStateM.Result ε σ α) :
    EStateM.bind p EStateM.pure = p := by
  funext s
  cases h : p s <;> simp [EStateM.bind, EStateM.pure, h]

set_option backward.isDefEq.respectTransparency false in
theorem composed_eq (varange : VARange) :
    GetGuestComposition.native varange = composed varange := by
  simp only [GetGuestComposition.native, composed, initial, d128, region, mair, mair2, aie, wxn, ps, ee, sif, dc, ntlsmd, nv1, cmow, ha, hd, ds, pie, pir, epan, pnch, haft, emec, Bind.bind, Pure.pure]
  with_unfolding_all simp only [state_bind_assoc, state_pure_bind, state_bind_pure]
  try rfl

theorem source_eq (varange : VARange) :
    AArch64_S1TTWParamsEL10 varange = composed varange := by
  rw [GetGuestComposition.complete, composed_eq]
#print axioms composed_eq
#print axioms source_eq
end GetGuestFields
