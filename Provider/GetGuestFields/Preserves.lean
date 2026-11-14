import GetGuestFields.ProofTool
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false
namespace GetGuestFields.Preserves
open Result

theorem mair2 (wp : S1TTWParams) : Returns (fun out => active out = active wp) (GetGuestFields.mair2 wp) := by
  unfold GetGuestFields.mair2
  preserve_guest_fields
#print axioms mair2

theorem wxn (wp : S1TTWParams) : Returns (fun out => active out = active wp) (GetGuestFields.wxn wp) := by
  unfold GetGuestFields.wxn
  preserve_guest_fields
#print axioms wxn

theorem ee (wp : S1TTWParams) : Returns (fun out => active out = active wp) (GetGuestFields.ee wp) := by
  unfold GetGuestFields.ee
  preserve_guest_fields
#print axioms ee

theorem sif (wp : S1TTWParams) : Returns (fun out => active out = active wp) (GetGuestFields.sif wp) := by
  unfold GetGuestFields.sif
  preserve_guest_fields
#print axioms sif

theorem dc (wp : S1TTWParams) : Returns (fun out => active out = active wp) (GetGuestFields.dc wp) := by
  unfold GetGuestFields.dc
  preserve_guest_fields
#print axioms dc

theorem ntlsmd (wp : S1TTWParams) : Returns (fun out => active out = active wp) (GetGuestFields.ntlsmd wp) := by
  unfold GetGuestFields.ntlsmd
  preserve_guest_fields
#print axioms ntlsmd

theorem nv1 (wp : S1TTWParams) : Returns (fun out => active out = active wp) (GetGuestFields.nv1 wp) := by
  unfold GetGuestFields.nv1
  preserve_guest_fields
#print axioms nv1

theorem cmow (wp : S1TTWParams) : Returns (fun out => active out = active wp) (GetGuestFields.cmow wp) := by
  unfold GetGuestFields.cmow
  preserve_guest_fields
#print axioms cmow

theorem ha (wp : S1TTWParams) : Returns (fun out => active out = active wp) (GetGuestFields.ha wp) := by
  unfold GetGuestFields.ha
  preserve_guest_fields
#print axioms ha

theorem hd (wp : S1TTWParams) : Returns (fun out => active out = active wp) (GetGuestFields.hd wp) := by
  unfold GetGuestFields.hd
  preserve_guest_fields
#print axioms hd

theorem pie (wp : S1TTWParams) : Returns (fun out => active out = active wp) (GetGuestFields.pie wp) := by
  unfold GetGuestFields.pie
  preserve_guest_fields
#print axioms pie

theorem pir (wp : S1TTWParams) : Returns (fun out => active out = active wp) (GetGuestFields.pir wp) := by
  unfold GetGuestFields.pir
  preserve_guest_fields
#print axioms pir

theorem epan (wp : S1TTWParams) : Returns (fun out => active out = active wp) (GetGuestFields.epan wp) := by
  unfold GetGuestFields.epan
  preserve_guest_fields
#print axioms epan

theorem haft (wp : S1TTWParams) : Returns (fun out => active out = active wp) (GetGuestFields.haft wp) := by
  unfold GetGuestFields.haft
  preserve_guest_fields
#print axioms haft

theorem emec (wp : S1TTWParams) : Returns (fun out => active out = active wp) (GetGuestFields.emec wp) := by
  unfold GetGuestFields.emec
  preserve_guest_fields
#print axioms emec
end GetGuestFields.Preserves
