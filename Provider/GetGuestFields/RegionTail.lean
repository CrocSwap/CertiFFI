import GetGuestFields.ProofTool
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option maxHeartbeats 300000
set_option maxRecDepth 1000000
set_option backward.isDefEq.respectTransparency false
namespace GetGuestFields.RegionTail

noncomputable def lower (walkparams : S1TTWParams) : SailM S1TTWParams := do
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
  pure walkparams

theorem lower_returns (wp : S1TTWParams) :
    Result.Returns (fun out => active out = active wp) (lower wp) := by
  unfold lower
  preserve_guest_fields
#print axioms lower_returns

noncomputable def upper (walkparams : S1TTWParams) : SailM S1TTWParams := do
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
  pure walkparams

theorem upper_returns (wp : S1TTWParams) :
    Result.Returns (fun out => active out = active wp) (upper wp) := by
  unfold upper
  preserve_guest_fields
#print axioms upper_returns
end GetGuestFields.RegionTail
