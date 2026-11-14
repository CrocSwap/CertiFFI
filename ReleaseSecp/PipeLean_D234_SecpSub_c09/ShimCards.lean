import PipeLean_D234_SecpSub_c09.ShimMath
import SecpShimShape
import SecpProofResult
import CertiFFIClaim.Premises
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmCert.Translate.Model.StaticPie
open TranslateSpan TranslateSpan.SecpRawDeployment HeapV2StepCerts NativeMteTagCheck ReleaseProfile ArmCertValue ArmCertPipe
open CertiFFI.Prog.Generic.ModelRunView DitShim243
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
open TranslateSpan TranslateSpan.SecpRawDeployment HeapV2StepCerts.RegBind
open CertiFFI.Prog.Generic.ModelRunView SecpMath XlateMath236.PhysicalOutput
open ReleaseProfile.SecpInputTransport
open ReleaseProfile.SecpShimCards
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 8192
namespace PipeLean_D234_SecpSub_c09.ShimCards

theorem card_run
    (real : Type)
[Sail.SailReal real]
(raw : CheckedTopology.Raw)
(config : AttributeConfig)
(rows : List PermissionRow)
(mapping : BitVec 64 → Option Nat)
(base : BitVec 64)
(pins : HeapV2E17.Pins)
(entry : NativeState)
(catalogue : NativeMteTagCheck.ControlCatalogue)
(globalTopology : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/global-topology" (CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true))
(bodyTopology : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/body-topology" (CheckedTopology.check raw (addresses EntryBinding.plan base entry) 4 = true))
(input_000 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/1/1" (base.toNat % 4096 = 0))
(input_001 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/1/2/1" (8136 % 4 = 0))
(input_002 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/1/2/2/1" (DitShim243.InitialCheck.rawPC EntryBinding.plan % 4 = 0))
(input_003 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/1/2/2/2/1" (17 + 1 = EntryBinding.plan.code.length))
(input_004 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/1/2/2/2/2/1" (List.Pairwise (fun x1 x2 => x1 ≠ x2) (List.map (fun x => x.logical) raw.logicalRows)))
(input_005 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/1/2/2/2/2/2/1" (entry.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + 16#64))
(input_006 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/1/2/2/2/2/2/2/1" ((BitVec.ofNat 64 pins.sp).toNat % 16 = 0))
(input_007 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/1/2/2/2/2/2/2/2/1" (Nat.le 2 (DefaultState.capacity entry+2)))
(input_008 : CertiFFI.Claim.CallerContract "card:secp-caller-return-lower" ((TranslateSpan.SecpRawDeployment.entryGPR entry 30).toNat.succ.le (2 ^ 55)))
(input_009 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/1/2/2/2/2/2/2/2/2/2/1" ((base + DitShim243.Geometry.shimPC 8136 7).toNat.succ.le (2 ^ 55)))
(input_010 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/1/2/2/2/2/2/2/2/2/2/2/1" ((base + DitShim243.InitialCheck.runOffset EntryBinding.plan 8136 17 base entry 7).toNat.succ.le (2 ^ 55)))
(input_011 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/1/2/2/2/2/2/2/2/2/2/2/2/1" (DitShim243.InitialCheck.runOffset EntryBinding.plan 8136 17 base entry 6 + sign_extend (67108270#26 +++ 0#2) 64 =
  DitShim243.InitialCheck.runOffset EntryBinding.plan 8136 17 base entry 7))
(input_012 : CertiFFI.Claim.Premise "card:secp-feature/103" .trm (entry.regs.FeatureImpl[103]! = true))
(input_013 : CertiFFI.Claim.Premise "card:secp-feature/123" .trm (entry.regs.FeatureImpl[123]! = true))
(input_014 : CertiFFI.Claim.Premise "card:secp-feature/227" .trm (entry.regs.FeatureImpl[227]! = false))
(input_015 : CertiFFI.Claim.Premise "card:secp-feature/2" .trm (entry.regs.FeatureImpl[2]! = false))
(input_016 : CertiFFI.Claim.Premise "card:secp-feature/3" .trm (entry.regs.FeatureImpl[3]! = false))
(input_017 : CertiFFI.Claim.Premise "card:secp-feature/6" .trm (entry.regs.FeatureImpl[6]! = true))
(input_018 : CertiFFI.Claim.Premise "card:secp-feature/7" .trm (entry.regs.FeatureImpl[7]! = true))
(input_019 : CertiFFI.Claim.Premise "card:secp-feature/230" .trm (entry.regs.FeatureImpl[230]! = false))
(input_020 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2" (ArmFull.Functions._get_SCR_EL3_Type_GCSEn (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) = 0#1))
(input_021 : CertiFFI.Claim.Premise "card:secp-feature/4" .trm (entry.regs.FeatureImpl[4]'(by decide) = true))
(input_022 : CertiFFI.Claim.Premise "card:secp-feature/232" .trm (entry.regs.FeatureImpl[232]'(by decide) = false))
(input_023 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/1" (entry.regs.bank_Bool ArmFull.Bank_Bool.SPESampleInFlight = false))
(input_024 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/1" (entry.regs.PSTATE.EL = 0#2))
(input_025 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/1" (entry.regs.PSTATE.nRW = 0#1))
(input_026 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/1" (ArmFull.Functions._get_EDECR_Type_RCE (entry.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32.EDECR) = 0#1))
(input_027 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/1" (ArmFull.Functions._get_CTIDEVCTL_Type_RCE (entry.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32.CTIDEVCTL) = 0#1))
(input_028 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/1" (ArmFull.Functions._get_EDSCR_Type_STATUS (entry.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32._EDSCR) = 2#6))
(input_029 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/2/1" (entry.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32.EDESR = 0#32))
(input_030 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/2/2/1" (entry.regs.__emulator_termination_opcode = none))
(input_031 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/2/2/2/1" (ArmFull.Functions._get_HCR_EL2_Type_E2H (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) = 1#1))
(input_032 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/2/2/2/2/1" (ArmFull.Functions._get_HCR_EL2_Type_TGE (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) = 1#1))
(input_033 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/2/2/2/2/2/1" (ArmFull.Functions._get_SCR_EL3_Type_NS (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) = 1#1))
(input_034 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (ArmFull.Functions._get_PMBLIMITR_EL1_Type_E (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.PMBLIMITR_EL1) = 0#1))
(input_035 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (ArmFull.Functions._get_MDSCR_EL1_Type_SS (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDSCR_EL1) = 0#1))
(input_036 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (Sail.BitVec.extractLsb (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.PMBSR_EL1) 17 17 = 0#1))
(input_037 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (entry.regs.PSTATE.A = 0#1))
(input_038 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (entry.regs.PSTATE.I = 0#1))
(input_039 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (entry.regs.PSTATE.F = 0#1))
(input_040 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (entry.regs.PSTATE.IL = 0#1))
(input_041 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (entry.regs.PSTATE.SS = 0#1))
(input_042 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (entry.regs.PSTATE.BTYPE = 0#2))
(input_043 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2" (entry.regs.BTypeNext = 0#2))
(input_044 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/1/2" (entry.regs.Branchtypetaken = ArmFull.BranchType.BranchType_RESET → False))
(input_045 : CertiFFI.Claim.Premise "card:secp-feature/0" .trm (entry.regs.FeatureImpl[0]'(by decide) = false))
(input_046 : CertiFFI.Claim.Premise "card:secp-feature/1" .trm (entry.regs.FeatureImpl[1]'(by decide) = false))
(input_047 : CertiFFI.Claim.Premise "card:secp-feature/2" .trm (entry.regs.FeatureImpl[2]'(by decide) = false))
(input_048 : CertiFFI.Claim.Premise "card:secp-feature/3" .trm (entry.regs.FeatureImpl[3]'(by decide) = false))
(input_049 : CertiFFI.Claim.Premise "card:secp-feature/5" .trm (entry.regs.FeatureImpl[5]'(by decide) = true))
(input_050 : CertiFFI.Claim.Premise "card:secp-feature/6" .trm (entry.regs.FeatureImpl[6]'(by decide) = true))
(input_051 : CertiFFI.Claim.Premise "card:secp-feature/7" .trm (entry.regs.FeatureImpl[7]'(by decide) = true))
(input_052 : CertiFFI.Claim.Premise "card:secp-feature/54" .trm (entry.regs.FeatureImpl[54]'(by decide) = true))
(input_053 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/1/1" (ArmFull.Functions._get_MDSCR_EL1_Type_MDE (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDSCR_EL1) = 0#1))
(input_054 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/1/2" (ArmFull.Functions._get_EDSCR_Type_HDE (entry.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32._EDSCR) = 0#1))
(input_055 : CertiFFI.Claim.Premise "card:secp-feature/4" .trm (ArmCert.HookQuiet.V0.feature entry.regs ArmFull.Feature.FEAT_AA64EL0 = true))
(input_056 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/1" (entry.regs.PSTATE.EL = 0#2))
(input_057 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/1" (entry.regs.PSTATE.nRW = 0#1))
(input_058 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/1" (ArmFull.Functions._get_SCR_EL3_Type_RW (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) = 1#1))
(input_059 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/2/1" (ArmFull.Functions._get_HCR_EL2_Type_RW (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) = 1#1))
(input_060 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/2/2/1" (ArmCert.HookQuiet.V0.feature entry.regs ArmFull.Feature.FEAT_RME = false ∨
  ArmFull.Functions._get_SCR_EL3_Type_NSE (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) = 0#1 ∨
    ArmCert.HookQuiet.V0.effectiveNS entry.regs = 1#1))
(input_061 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/2/2/2/1" (entry.regs.bank_Bool ArmFull.Bank_Bool.SPESampleInFlight = false))
(input_062 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/2/2/2/2/1" (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.PMINTENCLR_EL1 = 0#64))
(input_063 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/2/2/2/2/2/1" (ArmFull.Functions._get_BRBFCR_EL1_Type_PAUSED (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.BRBFCR_EL1) = 1#1))
(input_064 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/2/2/2/2/2/2/1" ((entry.regs.bank_Int ArmFull.Bank_Int.NUM_PMU_COUNTERS - 0).NonNeg))
(input_065 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/2/2/2/2/2/2/2/1" ((31 - entry.regs.bank_Int ArmFull.Bank_Int.NUM_PMU_COUNTERS).NonNeg))
(input_066 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/2/2/2/2/2/2/2/2/1" (ArmFull.Functions._get_CNTCR_Type_SCEN (entry.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32.CNTCR) = 0#1))
(input_067 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/2/2/2/2/2/2/2/2/2/1" (true = false ∨
  (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTP_CTL_EL0).getLsbD 0 = false ∨
    (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTP_CTL_EL0).getLsbD 1 = true ∨
      (ArmCert.HookQuiet.V0.realm entry.regs &&
            ArmFull.Functions._get_CNTHCTL_EL2_Type_CNTPMASK
                (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTHCTL_EL2) ==
              1#1) =
          true ∨
        ArmCert.HookQuiet.V0.Deadline (17 + 12) entry.regs (ArmCert.HookQuiet.V0.physicalOffset entry.regs)
          (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTP_CVAL_EL0)))
(input_068 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (true = false ∨
  (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTHP_CTL_EL2).getLsbD 0 = false ∨
    (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTHP_CTL_EL2).getLsbD 1 = true ∨
      false = true ∨
        ArmCert.HookQuiet.V0.Deadline (17 + 12) entry.regs (0#64)
          (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTHP_CVAL_EL2)))
(input_069 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (ArmCert.HookQuiet.V0.feature entry.regs ArmFull.Feature.FEAT_SEL2 = false ∨
  (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTHPS_CTL_EL2).getLsbD 0 = false ∨
    (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTHPS_CTL_EL2).getLsbD 1 = true ∨
      false = true ∨
        ArmCert.HookQuiet.V0.Deadline (17 + 12) entry.regs (0#64)
          (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTHPS_CVAL_EL2)))
(input_070 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (true = false ∨
  (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTPS_CTL_EL1).getLsbD 0 = false ∨
    (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTPS_CTL_EL1).getLsbD 1 = true ∨
      false = true ∨
        ArmCert.HookQuiet.V0.Deadline (17 + 12) entry.regs (ArmCert.HookQuiet.V0.physicalOffset entry.regs)
          (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTPS_CVAL_EL1)))
(input_071 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (true = false ∨
  (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTV_CTL_EL0).getLsbD 0 = false ∨
    (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTV_CTL_EL0).getLsbD 1 = true ∨
      (ArmCert.HookQuiet.V0.realm entry.regs &&
            ArmFull.Functions._get_CNTHCTL_EL2_Type_CNTVMASK
                (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTHCTL_EL2) ==
              1#1) =
          true ∨
        ArmCert.HookQuiet.V0.Deadline (17 + 12) entry.regs
          (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTVOFF_EL2)
          (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTV_CVAL_EL0)))
(input_072 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (ArmCert.HookQuiet.V0.feature entry.regs ArmFull.Feature.FEAT_VHE = false ∨
  (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTHV_CTL_EL2).getLsbD 0 = false ∨
    (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTHV_CTL_EL2).getLsbD 1 = true ∨
      false = true ∨
        ArmCert.HookQuiet.V0.Deadline (17 + 12) entry.regs (0#64)
          (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTHV_CVAL_EL2)))
(input_073 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2" ((ArmCert.HookQuiet.V0.feature entry.regs ArmFull.Feature.FEAT_SEL2 &&
      ArmCert.HookQuiet.V0.feature entry.regs ArmFull.Feature.FEAT_VHE) =
    false ∨
  (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTHVS_CTL_EL2).getLsbD 0 = false ∨
    (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTHVS_CTL_EL2).getLsbD 1 = true ∨
      false = true ∨
        ArmCert.HookQuiet.V0.Deadline (17 + 12) entry.regs (0#64)
          (ArmCert.HookQuiet.V0.reg64 entry.regs ArmFull.Bank_BitVec_64.CNTHVS_CVAL_EL2)))
(input_074 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/1" ((entry.regs.bank_Option_InterruptID ArmFull.Bank_Option_InterruptID.__GIC_Pending).isNone = true))
(input_075 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/1/1" (ArmFull.Functions._get_SCTLR_EL2_Type_E0E (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCTLR_EL2) = 0#1))
(input_076 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/1/2/1" (entry.regs.PSTATE.TCO = 0#1))
(input_077 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/1/2/2/1" (ArmFull.Functions._get_SCTLR_EL2_Type_TCF0 (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCTLR_EL2) = 0#2))
(input_078 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/1/2/2/2/1" (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2 = catalogue.tcrEL2))
(input_079 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/1/2/2/2/2/1" (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCTLR_EL2 = catalogue.sctlrEL2))
(input_080 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/1/2/2/2/2/2/1" (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2 = catalogue.hcrEL2))
(input_081 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/1/2/2/2/2/2/2" (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3 = catalogue.scrEL3))
(input_082 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/1/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), ArmCertWalk.NoUpdateRows
    (have __src := (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).params;
    ArmFull.S1TTWParams.mk __src.ha __src.hd __src.tbi __src.tbid __src.nfd __src.e0pd __src.d128 __src.aie __src.mair2
      __src.ds __src.ps __src.txsz __src.epan __src.dct __src.nv1 __src.cmow __src.pnch __src.disch
      (ArmCert.Translate.Model.hostHAFT entry.regs) __src.mtx __src.skl __src.pie __src.pir __src.pire0 __src.emec
      __src.amec __src.t0sz __src.t1sz __src.uwxn __src.tgx __src.irgn __src.orgn __src.sh __src.hpd __src.ee __src.wxn
      __src.ntlsmd __src.dc __src.sif __src.mair)
    (TranslateSpan.QueryDescriptors.data false) (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).imageRows =
  true))
(input_083 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/1/2" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), ArmCertWalk.NoUpdateRows
    (have __src := (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).params;
    ArmFull.S1TTWParams.mk __src.ha __src.hd __src.tbi __src.tbid __src.nfd __src.e0pd __src.d128 __src.aie __src.mair2
      __src.ds __src.ps __src.txsz __src.epan __src.dct __src.nv1 __src.cmow __src.pnch __src.disch
      (ArmCert.Translate.Model.hostHAFT entry.regs) __src.mtx __src.skl __src.pie __src.pir __src.pire0 __src.emec
      __src.amec __src.t0sz __src.t1sz __src.uwxn __src.tgx __src.irgn __src.orgn __src.sh __src.hpd __src.ee __src.wxn
      __src.ntlsmd __src.dc __src.sif __src.mair)
    (TranslateSpan.QueryDescriptors.data true) (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).imageRows =
  true))
(input_084 : CertiFFI.Claim.Premise "card:secp-feature/227" .trm (entry.regs.FeatureImpl[227]'(by decide) = false))
(input_085 : CertiFFI.Claim.Premise "card:secp-feature/111" .trm (entry.regs.FeatureImpl[111]'(by decide) = true))
(input_086 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/1/2/2" (ArmCertWalk.currentDCache entry.regs = true))
(input_087 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/1/1" (entry.regs.FeatureImpl[111]'(by decide) = (TranslateSpan.SecpRawDeployment.profile entry).lse2))
(input_088 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/1/2/1" (entry.regs.FeatureImpl[190]'(by decide) = (TranslateSpan.SecpRawDeployment.profile entry).lrcpc3))
(input_089 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/1/2/2" (ArmFull.Functions._get_SCTLR_EL2_Type_A (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCTLR_EL2) = 0#1))
(input_090 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/1" (entry.regs._PC = base + DitShim243.InitialCheck.runOffset EntryBinding.plan 8136 17 base entry 0))
(input_091 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), ArmCert.Translate.Model.checkPermissionRowsCovered rows (ArmCert.Translate.Model.rowsFootprint (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).imageRows) = true))
(input_092 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), ArmCert.Translate.Model.checkImage (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).imageRows ((CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).params.pie == 1#1) ((CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).params.ha == 1#1)
    ((CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).params.hd == 1#1) (ArmBridge.CruxGenGuarded.beforeFetchState entry).mem =
  true))
(input_093 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), ArmCert.Translate.Model.checkAttributeImage (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).imageRows config = true))
(input_094 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), ArmCert.Translate.Model.checkWriteBackAttributeImage (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).imageRows config = true))
(input_095 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), ArmCert.Translate.Model.checkPermissionImage rows (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).params (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs
    (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).controls (ArmBridge.CruxGenGuarded.beforeFetchState entry).mem =
  true))
(input_096 : CertiFFI.Claim.Premise "card:secp-feature/7" .trm ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.FeatureImpl[7]'(by decide) = true))
(input_097 : CertiFFI.Claim.Premise "card:secp-feature/3" .trm ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.FeatureImpl[3]'(by decide) = false))
(input_098 : CertiFFI.Claim.Premise "card:secp-feature/232" .trm ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.FeatureImpl[232]'(by decide) = false))
(input_099 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/1/2/2/2/1" ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.PSTATE.nRW = 0#1))
(input_100 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/1/2/2/2/2/1" (ArmFull.Functions._get_TCR_EL2_Type_TG0
    ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) =
  0#2))
(input_101 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/1/2/2/2/2/2/1" (ArmFull.Functions._get_HCR_EL2_Type_E2H
    ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) =
  1#1))
(input_102 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/1/2/2/2/2/2/2/1" ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.FeatureImpl[178]'(by decide) = true →
  ArmFull.Functions._get_TCR2_EL2_Type_D128
      ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR2_EL2) =
    0#1))
(input_103 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/1/2/2/2/2/2/2/2/1" ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.FeatureImpl[178]'(by decide) = true →
  ArmFull.Functions._get_TCR2_EL2_Type_AIE
      ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR2_EL2) =
    0#1))
(input_104 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/1/2/2/2/2/2/2/2/2/1" ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.FeatureImpl[178]'(by decide) = true →
  ArmFull.Functions._get_TCR2_EL2_Type_PnCH
      ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR2_EL2) =
    0#1))
(input_105 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/1/2/2/2/2/2/2/2/2/2" (Sail.BitVec.slice ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2)
    59 1 =
  0#1))
(input_106 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/1/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).controls.regime = S1LogicalReference.Regime.el20))
(input_107 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/1/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).controls.ha = (ArmCert.Translate.Model.hostHA (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs == 1#1)))
(input_108 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/1/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).controls.hd = (ArmCert.Translate.Model.hostHD (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs == 1#1)))
(input_109 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/1/2/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).controls.pie = (ArmCert.Translate.Model.hostPIE (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs == 1#1)))
(input_110 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/1/2/2/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).controls.hpd =
  ((if (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.FeatureImpl[48]'(by decide) = true then
      Sail.BitVec.extractLsb
        ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) 41 41
    else 0#1) ==
    1#1)))
(input_111 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/1/2/2/2/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).controls.pie = false ∨
  (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).controls.pir =
      ArmFull.Functions.Mk_S1PIRType
        ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.PIR_EL2) ∧
    (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).controls.pire0 =
      ArmFull.Functions.Mk_S1PIRType
        ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.PIRE0_EL2)))
(input_112 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/1/2/2/2/2/2/2" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), ((CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).controls.poe || (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).controls.e0poe) =
  ArmCertWalk.outputOverlayEnabled (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs))
(input_113 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/2/1/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).physicalConfig.paMax = 32 ∨
  (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).physicalConfig.paMax = 36 ∨
    (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).physicalConfig.paMax = 40 ∨
      (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).physicalConfig.paMax = 42 ∨
        (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).physicalConfig.paMax = 44 ∨
          (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).physicalConfig.paMax = 48 ∨
            (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).physicalConfig.paMax = 52 ∨ (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).physicalConfig.paMax = 56))
(input_114 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/2/1/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_Int ArmFull.Bank_Int.__supported_pa_size =
  (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).physicalConfig.paMax))
(input_115 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/2/1/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.FeatureImpl[69]'(by decide) = (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).physicalConfig.lpa))
(input_116 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/2/1/2/2/2" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.FeatureImpl[156]'(by decide) = (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).physicalConfig.lpa2))
(input_117 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).physicalConfig.ips =
  ArmFull.Functions._get_TCR_EL2_Type_IPS
    ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2)))
(input_118 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/2/1" (ArmFull.Functions._get_SCTLR_EL2_Type_EE
    ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCTLR_EL2) =
  0#1))
(input_119 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/2/2/1" (config.mair = (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MAIR_EL2))
(input_120 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/2/2/2/1" ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.FeatureImpl[166]'(by decide) = config.xs))
(input_121 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/2/2/2/2/1" ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.FeatureImpl[134]'(by decide) = config.mte2))
(input_122 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/2/2/2/2/2" ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.PSTATE.EL = 0#2 ∨
  (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.PSTATE.EL = 1#2))
(input_123 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (have __src := (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).params;
    ArmFull.S1TTWParams.mk __src.ha __src.hd __src.tbi __src.tbid __src.nfd __src.e0pd __src.d128 __src.aie __src.mair2
      __src.ds __src.ps
      (ArmFull.Functions._get_TCR_EL2_Type_T0SZ
        ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2))
      __src.epan __src.dct __src.nv1 __src.cmow __src.pnch __src.disch __src.haft __src.mtx __src.skl __src.pie
      __src.pir __src.pire0 __src.emec __src.amec __src.t0sz __src.t1sz __src.uwxn __src.tgx __src.irgn __src.orgn
      __src.sh __src.hpd __src.ee __src.wxn __src.ntlsmd __src.dc __src.sif __src.mair).ha =
  ArmCert.Translate.Model.hostHA (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs))
(input_124 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (have __src := (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).params;
    ArmFull.S1TTWParams.mk __src.ha __src.hd __src.tbi __src.tbid __src.nfd __src.e0pd __src.d128 __src.aie __src.mair2
      __src.ds __src.ps
      (ArmFull.Functions._get_TCR_EL2_Type_T0SZ
        ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2))
      __src.epan __src.dct __src.nv1 __src.cmow __src.pnch __src.disch __src.haft __src.mtx __src.skl __src.pie
      __src.pir __src.pire0 __src.emec __src.amec __src.t0sz __src.t1sz __src.uwxn __src.tgx __src.irgn __src.orgn
      __src.sh __src.hpd __src.ee __src.wxn __src.ntlsmd __src.dc __src.sif __src.mair).hd =
  ArmCert.Translate.Model.hostHD (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs))
(input_125 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (have __src := (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).params;
    ArmFull.S1TTWParams.mk __src.ha __src.hd __src.tbi __src.tbid __src.nfd __src.e0pd __src.d128 __src.aie __src.mair2
      __src.ds __src.ps
      (ArmFull.Functions._get_TCR_EL2_Type_T0SZ
        ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2))
      __src.epan __src.dct __src.nv1 __src.cmow __src.pnch __src.disch __src.haft __src.mtx __src.skl __src.pie
      __src.pir __src.pire0 __src.emec __src.amec __src.t0sz __src.t1sz __src.uwxn __src.tgx __src.irgn __src.orgn
      __src.sh __src.hpd __src.ee __src.wxn __src.ntlsmd __src.dc __src.sif __src.mair).pie =
  ArmCert.Translate.Model.hostPIE (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs))
(input_126 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (have __src := (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).params;
    ArmFull.S1TTWParams.mk __src.ha __src.hd __src.tbi __src.tbid __src.nfd __src.e0pd __src.d128 __src.aie __src.mair2
      __src.ds __src.ps
      (ArmFull.Functions._get_TCR_EL2_Type_T0SZ
        ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2))
      __src.epan __src.dct __src.nv1 __src.cmow __src.pnch __src.disch __src.haft __src.mtx __src.skl __src.pie
      __src.pir __src.pire0 __src.emec __src.amec __src.t0sz __src.t1sz __src.uwxn __src.tgx __src.irgn __src.orgn
      __src.sh __src.hpd __src.ee __src.wxn __src.ntlsmd __src.dc __src.sif __src.mair).wxn =
  ArmFull.Functions._get_SCTLR_EL2_Type_WXN
    ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCTLR_EL2)))
(input_127 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (have __src := (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).params;
    ArmFull.S1TTWParams.mk __src.ha __src.hd __src.tbi __src.tbid __src.nfd __src.e0pd __src.d128 __src.aie __src.mair2
      __src.ds __src.ps
      (ArmFull.Functions._get_TCR_EL2_Type_T0SZ
        ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2))
      __src.epan __src.dct __src.nv1 __src.cmow __src.pnch __src.disch __src.haft __src.mtx __src.skl __src.pie
      __src.pir __src.pire0 __src.emec __src.amec __src.t0sz __src.t1sz __src.uwxn __src.tgx __src.irgn __src.orgn
      __src.sh __src.hpd __src.ee __src.wxn __src.ntlsmd __src.dc __src.sif __src.mair).mtx =
  if (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.FeatureImpl[191]'(by decide) = true then
    Sail.BitVec.extractLsb
      ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) 60 60
  else 0#1))
(input_128 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/2/2" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (have __src := (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).params;
    ArmFull.S1TTWParams.mk __src.ha __src.hd __src.tbi __src.tbid __src.nfd __src.e0pd __src.d128 __src.aie __src.mair2
      __src.ds __src.ps
      (ArmFull.Functions._get_TCR_EL2_Type_T0SZ
        ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2))
      __src.epan __src.dct __src.nv1 __src.cmow __src.pnch __src.disch __src.haft __src.mtx __src.skl __src.pie
      __src.pir __src.pire0 __src.emec __src.amec __src.t0sz __src.t1sz __src.uwxn __src.tgx __src.irgn __src.orgn
      __src.sh __src.hpd __src.ee __src.wxn __src.ntlsmd __src.dc __src.sif __src.mair).txsz =
  ArmFull.Functions._get_TCR_EL2_Type_T0SZ
    ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2)))
(input_129 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).params.txsz =
  ArmCertWalk.normalizeTxsz (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs
    (ArmFull.Functions._get_TCR_EL2_Type_T0SZ
      ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2))))
(input_130 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), ArmCertWalk.translateGuardView (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).params =
  ArmCert.Translate.Model.currentHostGuardView (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs))
(input_131 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), ArmCertWalk.sourceTxszFault (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs
    (have __src := (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal).params;
    ArmFull.S1TTWParams.mk __src.ha __src.hd __src.tbi __src.tbid __src.nfd __src.e0pd __src.d128 __src.aie __src.mair2
      __src.ds __src.ps
      (ArmFull.Functions._get_TCR_EL2_Type_T0SZ
        ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2))
      __src.epan __src.dct __src.nv1 __src.cmow __src.pnch __src.disch __src.haft __src.mtx __src.skl __src.pie
      __src.pir __src.pire0 __src.emec __src.amec __src.t0sz __src.t1sz __src.uwxn __src.tgx __src.irgn __src.orgn
      __src.sh __src.hpd __src.ee __src.wxn __src.ntlsmd __src.dc __src.sif __src.mair) =
  false))
(input_132 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (ArmCertWalk.currentTranslationEnabled (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs = true))
(input_133 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/1/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2/2" ((ArmBridge.CruxGenGuarded.beforeFetchState entry).regs.bank_Bool ArmFull.Bank_Bool.__tlb_enabled = false))
(input_134 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/1" (TranslateSpan.MachineEntry.checkPlaced (TranslateSpan.SecpRawDeployment.codeOffsets (DitShim243.Deployment.extend EntryBinding.plan 8136 67108270#26))
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base mapping entry =
  true))
(input_135 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/1" (∀ (checkedGlobal : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 = true), TranslateSpan.CheckedEntry.checkQueries (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 checkedGlobal) config rows mapping 1030
    (DitShim243.Deployment.selectedQueries EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4
    (ArmBridge.CruxGenGuarded.beforeFetchState entry) =
  true))
(input_136 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/1" (∀ (checkedBody : CheckedTopology.check raw (addresses EntryBinding.plan base entry) 4 = true), TranslateSpan.CheckedEntry.checkQueries (CheckedTopology.spec raw (addresses EntryBinding.plan base entry) 4 checkedBody) config rows mapping 1030 (TranslateSpan.SecpRawDeployment.queries EntryBinding.plan base entry)
    4 (ArmBridge.CruxGenGuarded.beforeFetchState entry) =
  true))
(input_137 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/1" (TranslateSpan.MachineEntry.checkPresent EntryBinding.plan.regions (TranslateSpan.SecpRawDeployment.view EntryBinding.plan mapping entry) entry = true))
(input_138 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/1" (TranslateSpan.SecpRawDeployment.checkLayout (DitShim243.Deployment.extend EntryBinding.plan 8136 67108270#26) raw mapping base entry = true))
(input_139 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/1" (DitShim243.SlotCheck.check pins mapping (ArmCert.Translate.Model.rowsFootprint raw.imageRows) entry = true))
(input_140 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/1" (TranslateSpan.StaticLayout.checkCodeAvoid
    (TranslateSpan.SecpRawDeployment.codeOffsets (DitShim243.Deployment.extend EntryBinding.plan 8136 67108270#26)) mapping base
    (DitShim243.SlotCheck.slotByte pins mapping) =
  true))
(input_141 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/1" (DitShim243.SlotCheck.checkRegions pins mapping (TranslateSpan.SecpRawDeployment.view EntryBinding.plan mapping entry)
    (EntryBinding.plan.buffers +++ EntryBinding.plan.outputs) =
  true))
(input_142 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/1" (DitShim243.InitialCheck.checkWords (referenceImageI SecpArtifact.elf base (fun _ => 0)) 8136 67108270#26 = true))
(input_143 : CertiFFI.Claim.Premise "card:secp-feature/0" .trm (entry.regs.FeatureImpl[0]'(by decide) = false))
(input_144 : CertiFFI.Claim.Premise "card:secp-feature/1" .trm (entry.regs.FeatureImpl[1]'(by decide) = false))
(input_145 : CertiFFI.Claim.Premise "card:secp-feature/2" .trm (entry.regs.FeatureImpl[2]'(by decide) = false))
(input_146 : CertiFFI.Claim.Premise "card:secp-feature/3" .trm (entry.regs.FeatureImpl[3]'(by decide) = false))
(input_147 : CertiFFI.Claim.Premise "card:secp-feature/4" .trm (entry.regs.FeatureImpl[4]'(by decide) = true))
(input_148 : CertiFFI.Claim.Premise "card:secp-feature/5" .trm (entry.regs.FeatureImpl[5]'(by decide) = true))
(input_149 : CertiFFI.Claim.Premise "card:secp-feature/6" .trm (entry.regs.FeatureImpl[6]'(by decide) = true))
(input_150 : CertiFFI.Claim.Premise "card:secp-feature/7" .trm (entry.regs.FeatureImpl[7]'(by decide) = true))
(input_151 : CertiFFI.Claim.Premise "card:secp-feature/12" .trm (entry.regs.FeatureImpl[12]'(by decide) = true))
(input_152 : CertiFFI.Claim.Premise "card:secp-feature/153" .trm (entry.regs.FeatureImpl[153]'(by decide) = true))
(input_153 : CertiFFI.Claim.Premise "card:secp-feature/13" .trm (entry.regs.FeatureImpl[13]'(by decide) = true))
(input_154 : CertiFFI.Claim.Premise "card:secp-feature/143" .trm (entry.regs.FeatureImpl[143]'(by decide) = true))
(input_155 : CertiFFI.Claim.Premise "card:secp-feature/230" .trm (entry.regs.FeatureImpl[230]'(by decide) = false))
(input_156 : CertiFFI.Claim.Premise "card:secp-feature/123" .trm (entry.regs.FeatureImpl[123]'(by decide) = true))
(input_157 : CertiFFI.Claim.Premise "card:secp-feature/45" .trm (entry.regs.FeatureImpl[45]'(by decide) = true))
(input_158 : CertiFFI.Claim.Premise "card:secp-feature/144" .trm (entry.regs.FeatureImpl[144]'(by decide) = true))
(input_159 : CertiFFI.Claim.Premise "card:secp-feature/103" .trm (entry.regs.FeatureImpl[103]'(by decide) = true))
(input_160 : CertiFFI.Claim.Premise "card:secp-feature/60" .trm (entry.regs.FeatureImpl[60]'(by decide) = true))
(input_161 : CertiFFI.Claim.Premise "card:secp-feature/126" .trm (entry.regs.FeatureImpl[126]'(by decide) = true))
(input_162 : CertiFFI.Claim.Premise "card:secp-feature/185" .trm (entry.regs.FeatureImpl[185]'(by decide) = false))
(input_163 : CertiFFI.Claim.Premise "card:secp-feature/105" .trm (entry.regs.FeatureImpl[105]'(by decide) = true))
(input_164 : CertiFFI.Claim.Premise "card:secp-feature/145" .trm (entry.regs.FeatureImpl[145]'(by decide) = true))
(input_165 : CertiFFI.Claim.Premise "card:secp-feature/89" .trm (entry.regs.FeatureImpl[89]'(by decide) = true))
(input_166 : CertiFFI.Claim.Premise "card:secp-feature/107" .trm (entry.regs.FeatureImpl[107]'(by decide) = true))
(input_167 : CertiFFI.Claim.Premise "card:secp-feature/27" .trm (entry.regs.FeatureImpl[27]'(by decide) = true))
(input_168 : CertiFFI.Claim.Premise "card:secp-feature/65" .trm (entry.regs.FeatureImpl[65]'(by decide) = true))
(input_169 : CertiFFI.Claim.Premise "card:secp-feature/130" .trm (entry.regs.FeatureImpl[130]'(by decide) = true))
(input_170 : CertiFFI.Claim.Premise "card:secp-feature/108" .trm (entry.regs.FeatureImpl[108]'(by decide) = true))
(input_171 : CertiFFI.Claim.Premise "card:secp-feature/131" .trm (entry.regs.FeatureImpl[131]'(by decide) = true))
(input_172 : CertiFFI.Claim.Premise "card:secp-feature/67" .trm (entry.regs.FeatureImpl[67]'(by decide) = true))
(input_173 : CertiFFI.Claim.Premise "card:secp-feature/92" .trm (entry.regs.FeatureImpl[92]'(by decide) = true))
(input_174 : CertiFFI.Claim.Premise "card:secp-feature/93" .trm (entry.regs.FeatureImpl[93]'(by decide) = true))
(input_175 : CertiFFI.Claim.Premise "card:secp-feature/110" .trm (entry.regs.FeatureImpl[110]'(by decide) = true))
(input_176 : CertiFFI.Claim.Premise "card:secp-feature/50" .trm (entry.regs.FeatureImpl[50]'(by decide) = true))
(input_177 : CertiFFI.Claim.Premise "card:secp-feature/111" .trm (entry.regs.FeatureImpl[111]'(by decide) = true))
(input_178 : CertiFFI.Claim.Premise "card:secp-feature/171" .trm (entry.regs.FeatureImpl[171]'(by decide) = false))
(input_179 : CertiFFI.Claim.Premise "card:secp-feature/133" .trm (entry.regs.FeatureImpl[133]'(by decide) = true))
(input_180 : CertiFFI.Claim.Premise "card:secp-feature/95" .trm (entry.regs.FeatureImpl[95]'(by decide) = false))
(input_181 : CertiFFI.Claim.Premise "card:secp-feature/200" .trm (entry.regs.FeatureImpl[200]'(by decide) = false))
(input_182 : CertiFFI.Claim.Premise "card:secp-feature/36" .trm (entry.regs.FeatureImpl[36]'(by decide) = true))
(input_183 : CertiFFI.Claim.Premise "card:secp-feature/53" .trm (entry.regs.FeatureImpl[53]'(by decide) = true))
(input_184 : CertiFFI.Claim.Premise "card:secp-feature/232" .trm (entry.regs.FeatureImpl[232]'(by decide) = false))
(input_185 : CertiFFI.Claim.Premise "card:secp-feature/138" .trm (entry.regs.FeatureImpl[138]'(by decide) = true))
(input_186 : CertiFFI.Claim.Premise "card:secp-feature/40" .trm (entry.regs.FeatureImpl[40]'(by decide) = true))
(input_187 : CertiFFI.Claim.Premise "card:secp-feature/41" .trm (entry.regs.FeatureImpl[41]'(by decide) = true))
(input_188 : CertiFFI.Claim.Premise "card:secp-feature/76" .trm (entry.regs.FeatureImpl[76]'(by decide) = true))
(input_189 : CertiFFI.Claim.Premise "card:secp-feature/77" .trm (entry.regs.FeatureImpl[77]'(by decide) = true))
(input_190 : CertiFFI.Claim.Premise "card:secp-feature/78" .trm (entry.regs.FeatureImpl[78]'(by decide) = true))
(input_191 : CertiFFI.Claim.Premise "card:secp-feature/79" .trm (entry.regs.FeatureImpl[79]'(by decide) = true))
(input_192 : CertiFFI.Claim.Premise "card:secp-feature/233" .trm (entry.regs.FeatureImpl[233]'(by decide) = false))
(input_193 : CertiFFI.Claim.Premise "card:secp-feature/234" .trm (entry.regs.FeatureImpl[234]'(by decide) = false))
(input_194 : CertiFFI.Claim.Premise "card:secp-feature/235" .trm (entry.regs.FeatureImpl[235]'(by decide) = false))
(input_195 : CertiFFI.Claim.Premise "card:secp-feature/236" .trm (entry.regs.FeatureImpl[236]'(by decide) = false))
(input_196 : CertiFFI.Claim.Premise "card:secp-feature/81" .trm (entry.regs.FeatureImpl[81]'(by decide) = true))
(input_197 : CertiFFI.Claim.Premise "card:secp-feature/221" .trm (entry.regs.FeatureImpl[221]'(by decide) = true))
(input_198 : CertiFFI.Claim.Premise "card:secp-feature/222" .trm (entry.regs.FeatureImpl[222]'(by decide) = true))
(input_199 : CertiFFI.Claim.Premise "card:secp-feature/223" .trm (entry.regs.FeatureImpl[223]'(by decide) = true))
(input_200 : CertiFFI.Claim.Premise "card:secp-feature/224" .trm (entry.regs.FeatureImpl[224]'(by decide) = true))
(input_201 : CertiFFI.Claim.Premise "card:secp-feature/225" .trm (entry.regs.FeatureImpl[225]'(by decide) = true))
(input_202 : CertiFFI.Claim.Premise "card:secp-feature/226" .trm (entry.regs.FeatureImpl[226]'(by decide) = true))
(input_203 : CertiFFI.Claim.Premise "card:secp-feature/227" .trm (entry.regs.FeatureImpl[227]'(by decide) = false))
(input_204 : CertiFFI.Claim.Premise "card:secp-feature/165" .trm (entry.regs.FeatureImpl[165]'(by decide) = true))
(input_205 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/1/2/2/2/2/2" (entry.regs.bank_Int ArmFull.Bank_Int.NUM_BREAKPOINTS = 6))
(input_206 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/1/1/1/1" (entry.regs.bank_Int ArmFull.Bank_Int.NUM_WATCHPOINTS = 4))
(input_207 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/1/1/1/2" (entry.regs.bank_Int ArmFull.Bank_Int.__num_ctx_breakpoints = 2))
(input_208 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/1/1/2/1" (ArmFull.Functions._get_EDSCR_Type_STATUS (entry.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32._EDSCR) = 2#6))
(input_209 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/1/1/2/2/1" (entry.regs.bank_Bool ArmFull.Bank_Bool.SPESampleInFlight = false))
(input_210 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/1/1/2/2/2" (entry.regs.PSTATE.EL = 0#2))
(input_211 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/1/2/1/1" (entry.regs.PSTATE.nRW = 0#1))
(input_212 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/1/2/1/2" (entry.regs.PSTATE.IL = 0#1))
(input_213 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/1/2/2/1" (ArmFull.Functions._get_HCR_EL2_Type_E2H (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) = 1#1))
(input_214 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/1/2/2/2/1" (ArmFull.Functions._get_HCR_EL2_Type_TGE (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) = 1#1))
(input_215 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/1/2/2/2/2" (ArmFull.Functions._get_SCR_EL3_Type_NS (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) = 1#1))
(input_216 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/1/1/1" (ArmFull.Functions._get_SCR_EL3_Type_NSE (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) = 0#1))
(input_217 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/1/1/2" (ArmFull.Functions._get_MDSCR_EL1_Type_SS (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDSCR_EL1) = 0#1))
(input_218 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/1/2/1" (entry.regs.PSTATE.SS = 0#1))
(input_219 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/1/2/2/1" (ArmFull.Functions._get_EDESR_Type_OSUC (entry.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32.EDESR) = 0#1))
(input_220 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/1/2/2/2" (ArmFull.Functions._get_PMBLIMITR_EL1_Type_E (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.PMBLIMITR_EL1) = 0#1))
(input_221 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/2/1/1" (ArmFull.Functions._get_SCR_EL3_Type_RW (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) = 1#1))
(input_222 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/2/1/2/1" (ArmFull.Functions._get_SCR_EL3_Type_EEL2 (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) = 0#1))
(input_223 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/2/1/2/2" (ArmFull.Functions._get_TCR_EL2_Type_TBI0 (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) = 1#1))
(input_224 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/2/2/1" (ArmFull.Functions._get_TCR_EL2_Type_TBID0 (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) = 0#1))
(input_225 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/2/2/2/1" (ArmFull.Functions._get_MDCR_EL3_Type_NSPB (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDCR_EL3) = 3#2))
(input_226 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/1/2/2/2/2/2/2/2" (ArmFull.Functions._get_MDCR_EL3_Type_NSPBE (entry.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDCR_EL3) = 0#1))
(input_227 : CertiFFI.Claim.Premise "card:secp-feature/245" .trm (entry.regs.FeatureImpl[245]'(by decide) = false))
(input_228 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/2/2/1" (((TranslateSpan.SecpRawDeployment.sites EntryBinding.plan entry).all fun site =>
    TranslateSpan.SelectedLoadFacts.checkTargets mapping site.address) =
  true))
(input_229 : CertiFFI.Claim.DeploymentObligation "card:secp-shim-initial/leaf/2/2/2/2/2/2/2/2/2/2/2/2/2/2" (TranslateSpan.TagStatusRows.check (DefaultState.capacity entry+2) entry = true))
(caller : CertiFFI.Claim.CallerContract "card:secp-caller-lower-va-objects" (SecpCaller.Contract (SecpCaller.objects EntryBinding.plan entry)))
(hx : CertiFFI.Claim.CallerContract "card:secp-reduced-input/hx" ((SubSSA.inputLimbs (Default.inputs mapping entry) 0).value < modulus))
(hy : CertiFFI.Claim.CallerContract "card:secp-reduced-input/hy" ((SubSSA.inputLimbs (Default.inputs mapping entry) 0).value < modulus)) :
    proof_result% (ShimMath.run real raw config rows mapping base pins entry catalogue) := by
  have fields : Fields (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry 8136 67108270#26 (BitVec.ofNat 64 pins.sp)) 4 globalTopology.holds) (CheckedTopology.spec raw (addresses EntryBinding.plan base entry) 4 bodyTopology.holds) EntryBinding.plan raw config rows mapping base (referenceImageI SecpArtifact.elf base (fun _ => 0)) 8136 67108270#26 17 pins (DefaultState.capacity entry+2) entry catalogue := ⟨⟨input_000.holds,⟨input_001.holds,⟨input_002.holds,⟨input_003.holds,⟨input_004.holds,⟨input_005.holds,⟨input_006.holds,⟨input_007.holds,⟨input_008.holds,⟨input_009.holds,⟨input_010.holds,⟨input_011.holds,⟨input_012.holds,⟨input_013.holds,⟨input_014.holds,⟨input_015.holds,⟨input_016.holds,⟨input_017.holds,⟨input_018.holds,⟨input_019.holds,input_020.holds⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨input_021.holds,⟨input_022.holds,⟨input_023.holds,⟨input_024.holds,⟨input_025.holds,⟨input_026.holds,⟨input_027.holds,⟨input_028.holds,⟨input_029.holds,⟨input_030.holds,⟨input_031.holds,⟨input_032.holds,⟨input_033.holds,⟨input_034.holds,⟨input_035.holds,⟨input_036.holds,⟨input_037.holds,⟨input_038.holds,⟨input_039.holds,⟨input_040.holds,⟨input_041.holds,⟨input_042.holds,input_043.holds⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,input_044.holds⟩,⟨⟨input_045.holds,⟨input_046.holds,⟨input_047.holds,⟨input_048.holds,⟨input_049.holds,⟨input_050.holds,⟨input_051.holds,input_052.holds⟩⟩⟩⟩⟩⟩⟩,⟨⟨input_053.holds,input_054.holds⟩,⟨⟨input_055.holds,⟨input_056.holds,⟨input_057.holds,⟨input_058.holds,⟨input_059.holds,⟨input_060.holds,⟨input_061.holds,⟨input_062.holds,⟨input_063.holds,⟨input_064.holds,⟨input_065.holds,⟨input_066.holds,⟨input_067.holds,⟨input_068.holds,⟨input_069.holds,⟨input_070.holds,⟨input_071.holds,⟨input_072.holds,input_073.holds⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨input_074.holds,⟨⟨input_075.holds,⟨input_076.holds,⟨input_077.holds,⟨input_078.holds,⟨input_079.holds,⟨input_080.holds,input_081.holds⟩⟩⟩⟩⟩⟩,⟨⟨input_082.holds globalTopology.holds,input_083.holds globalTopology.holds⟩,⟨⟨input_084.holds,⟨input_085.holds,input_086.holds⟩⟩,⟨⟨input_087.holds,⟨input_088.holds,input_089.holds⟩⟩,⟨input_090.holds,⟨input_091.holds globalTopology.holds,⟨input_092.holds globalTopology.holds,⟨input_093.holds globalTopology.holds,⟨input_094.holds globalTopology.holds,⟨input_095.holds globalTopology.holds,⟨⟨⟨input_096.holds,⟨input_097.holds,⟨input_098.holds,⟨input_099.holds,⟨input_100.holds,⟨input_101.holds,⟨input_102.holds,⟨input_103.holds,⟨input_104.holds,input_105.holds⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨⟨input_106.holds globalTopology.holds,⟨input_107.holds globalTopology.holds,⟨input_108.holds globalTopology.holds,⟨input_109.holds globalTopology.holds,⟨input_110.holds globalTopology.holds,⟨input_111.holds globalTopology.holds,input_112.holds globalTopology.holds⟩⟩⟩⟩⟩⟩,⟨⟨input_113.holds globalTopology.holds,⟨input_114.holds globalTopology.holds,⟨input_115.holds globalTopology.holds,input_116.holds globalTopology.holds⟩⟩⟩,⟨input_117.holds globalTopology.holds,⟨input_118.holds,⟨input_119.holds,⟨input_120.holds,⟨input_121.holds,input_122.holds⟩⟩⟩⟩⟩⟩⟩⟩,⟨⟨input_123.holds globalTopology.holds,⟨input_124.holds globalTopology.holds,⟨input_125.holds globalTopology.holds,⟨input_126.holds globalTopology.holds,⟨input_127.holds globalTopology.holds,input_128.holds globalTopology.holds⟩⟩⟩⟩⟩,⟨input_129.holds globalTopology.holds,⟨input_130.holds globalTopology.holds,⟨input_131.holds globalTopology.holds,⟨input_132.holds,input_133.holds⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨input_134.holds,⟨input_135.holds globalTopology.holds,⟨input_136.holds bodyTopology.holds,⟨input_137.holds,⟨input_138.holds,⟨input_139.holds,⟨input_140.holds,⟨input_141.holds,⟨input_142.holds,⟨⟨⟨⟨⟨⟨⟨input_143.holds,input_144.holds⟩,⟨input_145.holds,⟨input_146.holds,input_147.holds⟩⟩⟩,⟨⟨input_148.holds,input_149.holds⟩,⟨input_150.holds,⟨input_151.holds,input_152.holds⟩⟩⟩⟩,⟨⟨⟨input_153.holds,input_154.holds⟩,⟨input_155.holds,⟨input_156.holds,input_157.holds⟩⟩⟩,⟨⟨input_158.holds,⟨input_159.holds,input_160.holds⟩⟩,⟨input_161.holds,⟨input_162.holds,input_163.holds⟩⟩⟩⟩⟩,⟨⟨⟨⟨input_164.holds,input_165.holds⟩,⟨input_166.holds,⟨input_167.holds,input_168.holds⟩⟩⟩,⟨⟨input_169.holds,input_170.holds⟩,⟨input_171.holds,⟨input_172.holds,input_173.holds⟩⟩⟩⟩,⟨⟨⟨input_174.holds,input_175.holds⟩,⟨input_176.holds,⟨input_177.holds,input_178.holds⟩⟩⟩,⟨⟨input_179.holds,⟨input_180.holds,input_181.holds⟩⟩,⟨input_182.holds,⟨input_183.holds,input_184.holds⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨input_185.holds,input_186.holds⟩,⟨input_187.holds,⟨input_188.holds,input_189.holds⟩⟩⟩,⟨⟨input_190.holds,input_191.holds⟩,⟨input_192.holds,⟨input_193.holds,input_194.holds⟩⟩⟩⟩,⟨⟨⟨input_195.holds,input_196.holds⟩,⟨input_197.holds,⟨input_198.holds,input_199.holds⟩⟩⟩,⟨⟨input_200.holds,⟨input_201.holds,input_202.holds⟩⟩,⟨input_203.holds,⟨input_204.holds,input_205.holds⟩⟩⟩⟩⟩,⟨⟨⟨⟨input_206.holds,input_207.holds⟩,⟨input_208.holds,⟨input_209.holds,input_210.holds⟩⟩⟩,⟨⟨input_211.holds,input_212.holds⟩,⟨input_213.holds,⟨input_214.holds,input_215.holds⟩⟩⟩⟩,⟨⟨⟨input_216.holds,input_217.holds⟩,⟨input_218.holds,⟨input_219.holds,input_220.holds⟩⟩⟩,⟨⟨input_221.holds,⟨input_222.holds,input_223.holds⟩⟩,⟨input_224.holds,⟨input_225.holds,input_226.holds⟩⟩⟩⟩⟩⟩⟩,⟨input_227.holds,⟨input_228.holds,input_229.holds⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have checked : ShimMath.check raw config rows mapping base pins entry catalogue = true :=
    (check_iff EntryBinding.plan raw config rows mapping base (referenceImageI SecpArtifact.elf base (fun _ => 0)) 8136 67108270#26 17 pins (DefaultState.capacity entry+2) entry catalogue).mpr ⟨globalTopology.holds,bodyTopology.holds,fields⟩
  exact ShimMath.run real raw config rows mapping base pins entry catalogue checked hx.holds hy.holds

theorem card_run_root : type_of% @PipeLean_D234_SecpSub_c09.ShimMath.run := by
  intro real inst raw config rows mapping base pins entry catalogue checked hx hy
  obtain ⟨gt,rt,fields⟩ := (check_iff EntryBinding.plan raw config rows mapping base (referenceImageI SecpArtifact.elf base (fun _ => 0)) 8136 67108270#26 17 pins (DefaultState.capacity entry+2) entry catalogue).mp checked
  have caller := caller_of_fields _ _ EntryBinding.plan raw config rows mapping base (referenceImageI SecpArtifact.elf base (fun _ => 0)) 8136 67108270#26 17 pins (DefaultState.capacity entry+2) entry catalogue fields
  exact @card_run real inst raw config rows mapping base pins entry catalogue ⟨gt⟩ ⟨rt⟩
    ⟨fields.1.1⟩ ⟨fields.1.2.1⟩ ⟨fields.1.2.2.1⟩ ⟨fields.1.2.2.2.1⟩ ⟨fields.1.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩ ⟨fields.2.1.1.1.1⟩ ⟨fields.2.1.1.1.2.1⟩ ⟨fields.2.1.1.1.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩ ⟨fields.2.1.1.2⟩ ⟨fields.2.1.2.1.1⟩ ⟨fields.2.1.2.1.2.1⟩ ⟨fields.2.1.2.1.2.2.1⟩ ⟨fields.2.1.2.1.2.2.2.1⟩ ⟨fields.2.1.2.1.2.2.2.2.1⟩ ⟨fields.2.1.2.1.2.2.2.2.2.1⟩ ⟨fields.2.1.2.1.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.1.2.2.2.2.2.2.2⟩ ⟨fields.2.1.2.2.1.1⟩ ⟨fields.2.1.2.2.1.2⟩ ⟨fields.2.1.2.2.2.1.1⟩ ⟨fields.2.1.2.2.2.1.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩ ⟨fields.2.1.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.1.1⟩ ⟨fields.2.1.2.2.2.2.2.1.2.1⟩ ⟨fields.2.1.2.2.2.2.2.1.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.1.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.1.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.1.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.1.2.2.2.2.2.2⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.1.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.1.2⟩ ⟨fields.2.1.2.2.2.2.2.2.2.1.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.1.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.1.2.2⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.1.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.1.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.1.2.2⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.2.2.2.2.2.2⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.2.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.2.2.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.2.2.2.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.2.2.2.2.2⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1.2.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1.2.2.2⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fun _ => fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩ ⟨fields.2.2.1⟩ ⟨fun _ => fields.2.2.2.1⟩ ⟨fun _ => fields.2.2.2.2.1⟩ ⟨fields.2.2.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.1.1.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.1.1.1.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.1.1.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.1.1.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.1.1.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.1.2.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.1.2.1.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.1.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.1.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.1.2.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.2.1.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.2.1.1.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.2.1.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.2.1.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.2.1.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.2.2.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.2.2.1.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.2.2.1.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.2.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.1.2.2.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.1.1.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.1.1.1.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.1.1.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.1.1.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.1.1.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.1.2.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.1.2.1.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.1.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.1.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.1.2.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.1.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.1.1.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.1.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.1.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.1.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.1.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.1.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.1.1.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.1.1.1.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.1.1.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.1.1.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.1.1.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.1.2.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.1.2.1.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.1.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.1.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.1.2.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.1.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.1.1.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.1.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.1.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.1.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.2.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.2.1.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.2.1.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.2.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1.1.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1.1.1.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1.1.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1.1.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1.1.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1.2.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1.2.1.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1.2.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1.1.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ ⟨fields.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩ ⟨caller⟩ ⟨hx⟩ ⟨hy⟩

#print axioms card_run
#print axioms card_run_root
#print premises card_run
end PipeLean_D234_SecpSub_c09.ShimCards
