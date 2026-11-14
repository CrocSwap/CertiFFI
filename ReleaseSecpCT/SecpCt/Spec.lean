-- secp CT0: EvShape depends on the checked spec only through raw.logicalRows / raw.layout.
import SecpCt.EvClass
import TranslateSpan.CheckedTopology
open ArmCert.Translate ArmCert.Translate.Model ArmBridge.Draft ArmBridge.CruxGenGuarded
set_option autoImplicit false
namespace SecpCt

theorem evshape_spec (raw : TranslateSpan.CheckedTopology.Raw) (A B : List (BitVec 64))
    (hA : TranslateSpan.CheckedTopology.check raw A 4 = true) (hB : TranslateSpan.CheckedTopology.check raw B 4 = true)
    (mapping : BitVec 64 → Option Nat) (data : List (Option ArmCertCTOrdered.OrderedEventV2.Record)) (x fin : NativeState)
    (e : StepEvents.EvShape (TranslateSpan.CheckedTopology.spec raw A 4 hA) mapping data x fin) :
    StepEvents.EvShape (TranslateSpan.CheckedTopology.spec raw B 4 hB) mapping data x fin := by
  obtain ⟨n, T, D, ev, tr, mp, dr⟩ := e
  exact ⟨n, T, D, ev, tr, mp, dr⟩

end SecpCt
#print axioms SecpCt.evshape_spec
