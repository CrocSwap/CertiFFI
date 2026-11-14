import GetGuestFields.ProofTool
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace GetGuestFields.Normal
open S1Normality

theorem initial : Normal (GetGuestFields.initial) := by
  unfold GetGuestFields.initial
  preserve_guest_fields
#print axioms initial

theorem d128 (wp : S1TTWParams) : Normal (GetGuestFields.d128 wp) := by
  unfold GetGuestFields.d128
  preserve_guest_fields
#print axioms d128

theorem region (wp : S1TTWParams) (vr : VARange) : Normal (GetGuestFields.region wp vr) := by
  unfold GetGuestFields.region
  preserve_guest_fields
#print axioms region

theorem mair (wp : S1TTWParams) : Normal (GetGuestFields.mair wp) := by
  unfold GetGuestFields.mair
  preserve_guest_fields
#print axioms mair

theorem mair2 (wp : S1TTWParams) : Normal (GetGuestFields.mair2 wp) := by
  unfold GetGuestFields.mair2
  preserve_guest_fields
#print axioms mair2

theorem aie (wp : S1TTWParams) : Normal (GetGuestFields.aie wp) := by
  unfold GetGuestFields.aie
  preserve_guest_fields
#print axioms aie

theorem wxn (wp : S1TTWParams) : Normal (GetGuestFields.wxn wp) := by
  unfold GetGuestFields.wxn
  preserve_guest_fields
#print axioms wxn

theorem ps (wp : S1TTWParams) : Normal (GetGuestFields.ps wp) := by
  unfold GetGuestFields.ps
  preserve_guest_fields
#print axioms ps

theorem ee (wp : S1TTWParams) : Normal (GetGuestFields.ee wp) := by
  unfold GetGuestFields.ee
  preserve_guest_fields
#print axioms ee

theorem sif (wp : S1TTWParams) : Normal (GetGuestFields.sif wp) := by
  unfold GetGuestFields.sif
  preserve_guest_fields
#print axioms sif

theorem dc (wp : S1TTWParams) : Normal (GetGuestFields.dc wp) := by
  unfold GetGuestFields.dc
  preserve_guest_fields
#print axioms dc

theorem ntlsmd (wp : S1TTWParams) : Normal (GetGuestFields.ntlsmd wp) := by
  unfold GetGuestFields.ntlsmd
  preserve_guest_fields
#print axioms ntlsmd

theorem nv1 (wp : S1TTWParams) : Normal (GetGuestFields.nv1 wp) := by
  unfold GetGuestFields.nv1
  preserve_guest_fields
#print axioms nv1

theorem cmow (wp : S1TTWParams) : Normal (GetGuestFields.cmow wp) := by
  unfold GetGuestFields.cmow
  preserve_guest_fields
#print axioms cmow

theorem ha (wp : S1TTWParams) : Normal (GetGuestFields.ha wp) := by
  unfold GetGuestFields.ha
  preserve_guest_fields
#print axioms ha

theorem hd (wp : S1TTWParams) : Normal (GetGuestFields.hd wp) := by
  unfold GetGuestFields.hd
  preserve_guest_fields
#print axioms hd

theorem ds (wp : S1TTWParams) : Normal (GetGuestFields.ds wp) := by
  unfold GetGuestFields.ds
  preserve_guest_fields
#print axioms ds

theorem pie (wp : S1TTWParams) : Normal (GetGuestFields.pie wp) := by
  unfold GetGuestFields.pie
  preserve_guest_fields
#print axioms pie

theorem pir (wp : S1TTWParams) : Normal (GetGuestFields.pir wp) := by
  unfold GetGuestFields.pir
  preserve_guest_fields
#print axioms pir

theorem epan (wp : S1TTWParams) : Normal (GetGuestFields.epan wp) := by
  unfold GetGuestFields.epan
  preserve_guest_fields
#print axioms epan

theorem pnch (wp : S1TTWParams) : Normal (GetGuestFields.pnch wp) := by
  unfold GetGuestFields.pnch
  preserve_guest_fields
#print axioms pnch

theorem haft (wp : S1TTWParams) : Normal (GetGuestFields.haft wp) := by
  unfold GetGuestFields.haft
  preserve_guest_fields
#print axioms haft

theorem emec (wp : S1TTWParams) : Normal (GetGuestFields.emec wp) := by
  unfold GetGuestFields.emec
  preserve_guest_fields
#print axioms emec

end GetGuestFields.Normal
