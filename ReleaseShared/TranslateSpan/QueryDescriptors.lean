-- Fixed pure representatives; oracle-varying fields are handled by AccAgree.
import ArmCertTranslateModel.ClosedTable
open Sail ArmFull ArmFull.Functions ArmCert.Translate.Model
set_option autoImplicit false
namespace TranslateSpan.QueryDescriptors

def data (write : Bool) : AccessDescriptor :=
  { (default : AccessDescriptor) with
    acctype := .AccessType_GPR
    el := EL0
    ss := .SS_NonSecure
    read := !write
    write := write
    tagaccess := false
    transactional := false
    nonfault := false
    contiguous := false
    firstfault := false
    first := false
    ls64 := false }

def fetch : AccessDescriptor :=
  { (default : AccessDescriptor) with
    acctype := .AccessType_IFETCH
    el := EL0
    ss := .SS_NonSecure
    read := false
    write := false
    tagaccess := false
    transactional := false
    nonfault := false
    contiguous := false
    firstfault := false
    first := false
    ls64 := false }

theorem data_shape (write : Bool) : DataShape write (data write) := by
  constructor <;> rfl

theorem fetch_shape : FetchShape fetch := by
  constructor <;> rfl

#print axioms data
#print axioms fetch
#print axioms data_shape
#print axioms fetch_shape
end TranslateSpan.QueryDescriptors
