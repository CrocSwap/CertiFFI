-- Memory (runtime14 CT, 4b0921b): the step's own events of a memory tail. fin.events = f.events ++ delta, whose
-- records under nodup are `data` (the data access record and its translation traffic: HeapV2StepCerts.DataRecs.dataRecs).
import HeapV2StepCerts.DataRecs
set_option autoImplicit false
namespace ArmCertMemPipe
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmCert.Translate.Model ArmBridge.Draft

def EvD {domain : QueryDomain} (spec : TopologyImageSpec domain) (data : List (Option ArmCertCTOrdered.OrderedEventV2.Record))
    (f fin : NativeState) : Prop :=
  ∃ delta : Array Event, fin.events = f.events ++ delta ∧
    ((spec.logicalRows.map (·.logical)).Nodup → delta.toList.map ArmCertCTOrdered.OrderedEventV2.record = data)

end ArmCertMemPipe
