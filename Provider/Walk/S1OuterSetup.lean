import Walk.S1ResourcePath
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
namespace S1OuterSetup
abbrev State := S1OuterBody.State
abbrev Vars := S1OuterBody.Vars
structure Context where
  wp : S1TTWParams
  va : BitVec 64
  regime : Regime
  acc : AccessDescriptor
  startlevel : Int
  cfg : S2Interface.Config
  regimes : S1LeafBoth.Regimes regime
  d128 : wp.d128 = 0#1
  ds : wp.ds = 0#1
  tg : wp.tgx = .TGx_4KB
  aie : wp.aie = 0#1
  mair : wp.mair = 0x000000040044ffff#64
  vm : _get_HCR_EL2_Type_VM cfg.hcr = 0#1
  dc : _get_HCR_EL2_Type_DC cfg.hcr = 0#1
  ss : acc.ss = .SS_NonSecure
structure Ready (c : Context) (s : State) : Prop where
  pa : s.regs.bank_Int .__supported_pa_size = 48
  config : S2Interface.ConfigAt c.cfg s
  el : s.regs.PSTATE.EL = 0#2 ∨ s.regs.PSTATE.EL = 1#2
  noRME : s.regs.FeatureImpl[232] = false
  a64 : s.regs.PSTATE.nRW = 0#1
  el3A64 : s.regs.FeatureImpl[7] = true
  noEL3A32 : s.regs.FeatureImpl[3] = false

theorem Ready.of_regs {c : Context} {s t : State} (h : Ready c s) (hr : t.regs = s.regs) :
    Ready c t := by
  rcases h with ⟨hp, hc, he, hn, ha, h3, h32⟩
  have hc' : S2Interface.ConfigAt c.cfg t := by
    rcases hc with ⟨a, b, c, d, e, f, g, h⟩
    exact ⟨by simpa only [hr] using a, by simpa only [hr] using b,
      by simpa only [hr] using c, by simpa only [hr] using d,
      by simpa only [hr] using e, by simpa only [hr] using f,
      by simpa only [hr] using g, by simpa only [hr] using h⟩
  exact ⟨by simpa only [hr] using hp, hc', by simpa only [hr] using he,
    by simpa only [hr] using hn, by simpa only [hr] using ha,
    by simpa only [hr] using h3, by simpa only [hr] using h32⟩

def current : Vars → TTWState | (_, _, _, _, _, _, _, _, _, w) => w
def fault : Vars → FaultRecord | (_, _, _, _, f, _, _, _, _, _) => f
def slot : Vars → FullAddress | (_, addr, _, _, _, _, _, _, _, _) => addr
def stop : Vars → Bool | (_, _, _, typ, _, _, _, _, _, _) => typ == .DescriptorType_Leaf
#print axioms Ready.of_regs
end S1OuterSetup
