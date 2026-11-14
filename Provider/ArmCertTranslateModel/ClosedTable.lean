import ArmCertTranslateModel.ClosedMembershipTransport
import ArmCertWalk.AccessTransfer

/-! E17 instance table from representatives: closed query membership for a consumer
map whose permitted descriptors are stated by SHAPE (every oracle-varying descriptor
variant), from one evaluated representative query per declared access. Uses Memory's
AccAgree transfers (the varying fields are read by no current check). -/

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- Every permitted access has an in-domain representative at the same VA whose
    descriptor agrees and whose current access data holds at `state`. -/
def RepresentedAt {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (state : State) : Prop :=
  ∀ va acc aligned size, m.permitted va acc aligned size →
    domain ⟨va, ⟨acc, aligned⟩, size⟩ ∧
    ∃ (r : S1LogicalReference.Request) (data : S1AccessData spec config rows ⟨va, r, size⟩),
      AccAgree r.raw acc ∧ CurrentS1AccessAt spec config rows mapping ⟨va, r, size⟩ data state

theorem closed_of_represented {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {state : State}
    (represented : RepresentedAt spec config rows mapping m state) :
    ClosedMembershipAt spec config rows mapping m state := by
  intro va acc aligned size permitted
  obtain ⟨member, r, data, agree, current⟩ := represented va acc aligned size permitted
  exact ⟨⟨va, ⟨acc, aligned⟩, size⟩, rfl, rfl, rfl, rfl, member,
    S1AccessData.transfer (r' := ⟨acc, aligned⟩) data agree,
    CurrentS1AccessAt.transfer (r' := ⟨acc, aligned⟩) current agree⟩

/-- Descriptor shape of an EL0 non-secure ordinary GPR data access (read or write). -/
structure DataShape (write : Bool) (acc : AccessDescriptor) : Prop where
  acctype : acc.acctype = .AccessType_GPR
  el : acc.el = EL0
  ss : acc.ss = .SS_NonSecure
  read : acc.read = !write
  write : acc.write = write
  tagaccess : acc.tagaccess = false
  transactional : acc.transactional = false
  nonfault : acc.nonfault = false
  contiguous : acc.contiguous = false
  firstfault : acc.firstfault = false
  first : acc.first = false
  ls64 : acc.ls64 = false

/-- Descriptor shape of an EL0 non-secure instruction fetch. -/
structure FetchShape (acc : AccessDescriptor) : Prop where
  acctype : acc.acctype = .AccessType_IFETCH
  el : acc.el = EL0
  ss : acc.ss = .SS_NonSecure
  read : acc.read = false
  write : acc.write = false
  tagaccess : acc.tagaccess = false
  transactional : acc.transactional = false
  nonfault : acc.nonfault = false
  contiguous : acc.contiguous = false
  firstfault : acc.firstfault = false
  first : acc.first = false
  ls64 : acc.ls64 = false

theorem DataShape.agree {write : Bool} {a b : AccessDescriptor} (ha : DataShape write a)
    (hb : DataShape write b) : AccAgree a b :=
  ⟨ha.acctype.trans hb.acctype.symm, ha.el.trans hb.el.symm, ha.ss.trans hb.ss.symm,
    ha.read.trans hb.read.symm, ha.write.trans hb.write.symm, ha.tagaccess.trans hb.tagaccess.symm,
    ha.transactional.trans hb.transactional.symm, ha.nonfault.trans hb.nonfault.symm,
    ha.contiguous.trans hb.contiguous.symm, ha.firstfault.trans hb.firstfault.symm,
    ha.first.trans hb.first.symm, ha.ls64.trans hb.ls64.symm⟩

theorem FetchShape.agree {a b : AccessDescriptor} (ha : FetchShape a) (hb : FetchShape b) : AccAgree a b :=
  ⟨ha.acctype.trans hb.acctype.symm, ha.el.trans hb.el.symm, ha.ss.trans hb.ss.symm,
    ha.read.trans hb.read.symm, ha.write.trans hb.write.symm, ha.tagaccess.trans hb.tagaccess.symm,
    ha.transactional.trans hb.transactional.symm, ha.nonfault.trans hb.nonfault.symm,
    ha.contiguous.trans hb.contiguous.symm, ha.firstfault.trans hb.firstfault.symm,
    ha.first.trans hb.first.symm, ha.ls64.trans hb.ls64.symm⟩

#print axioms closed_of_represented
#print axioms DataShape.agree
#print axioms FetchShape.agree
end ArmCert.Translate.Model
