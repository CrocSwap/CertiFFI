import ReleaseProfile.MachineSource.Recipe
import ReleaseProfile.MachineSource.Coordinates

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024

namespace ReleaseProfile.GB10.FeatureSource

open ReleaseProfile.MachineSource

#check "CURRENT_DECL FeatureSource.declared"
/-- Declared values retain scoped authority obligations; this is not an acquisition proof. -/
def declared (index : Fin 259) : Option (Bool × AuthorityRef) :=
  match index.val with
  | 0 => some (false, ⟨"GB10-TABLE-D244/raw-feature/0", .rawTrm⟩)
  | 1 => some (false, ⟨"GB10-TABLE-D244/raw-feature/1", .rawTrm⟩)
  | 2 => some (false, ⟨"GB10-TABLE-D244/raw-feature/2", .rawTrm⟩)
  | 3 => some (false, ⟨"GB10-TABLE-D244/raw-feature/3", .rawTrm⟩)
  | 4 => some (true, ⟨"GB10-TABLE-D244/raw-feature/4", .rawTrm⟩)
  | 5 => some (true, ⟨"GB10-TABLE-D244/raw-feature/5", .rawTrm⟩)
  | 6 => some (true, ⟨"GB10-TABLE-D244/raw-feature/6", .rawTrm⟩)
  | 7 => some (true, ⟨"GB10-TABLE-D244/raw-feature/7", .rawTrm⟩)
  | 8 => some (true, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:23016,a725:23612/ID_AA64PFR0_EL1.EL0=0b0001", .rawTrm⟩)
  | 9 => some (true, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:23013,a725:23609/ID_AA64PFR0_EL1.EL1=0b0001", .rawTrm⟩)
  | 10 => some (true, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:23010,a725:23606/ID_AA64PFR0_EL1.EL2=0b0001", .rawTrm⟩)
  | 11 => some (true, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:22995,a725:23603/ID_AA64PFR0_EL1.EL3=0b0001", .rawTrm⟩)
  | 12 => some (true, ⟨"GB10-TABLE-D244/raw-feature/12", .conditionalTrm⟩)
  | 13 => some (true, ⟨"GB10-TABLE-D244/raw-feature/13", .rawTrm⟩)
  | 14 => some (false, ⟨"GB10-TABLE-D244/raw-feature/14", .rawTrm⟩)
  | 15 => some (false, ⟨"GB10-TABLE-D244/raw-feature/15", .rawTrm⟩)
  | 16 => some (true, ⟨"GB10-TABLE-D244/raw-feature/16", .rawTrm⟩)
  | 17 => some (false, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:22934,a725:23533/ID_AA64PFR0_EL1.CSV2=0b0010", .rawTrm⟩)
  | 18 => some (false, ⟨"GB10-TABLE-D244/raw-feature/18", .rawTrm⟩)
  | 26 => some (false, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:24755,a725:25208/ID_AA64MMFR1_EL1.ETS=0b0001", .rawTrm⟩)
  | 27 => some (true, ⟨"GB10-TABLE-D244/raw-feature/27", .rawTrm⟩)
  | 35 => some (false, ⟨"GB10-TABLE-D244/raw-feature/35", .rawTrm⟩)
  | 36 => some (true, ⟨"GB10-TABLE-D244/raw-feature/36", .conditionalTrm⟩)
  | 37 => some (true, ⟨"GB10-TABLE-D244/raw-feature/37", .rawTrm⟩)
  | 40 => some (true, ⟨"GB10-TABLE-D244/raw-feature/40", .conditionalTrm⟩)
  | 41 => some (true, ⟨"GB10-TABLE-D244/raw-feature/41", .conditionalTrm⟩)
  | 44 => some (true, ⟨"GB10-TABLE-D244/raw-feature/44", .rawTrm⟩)
  | 45 => some (true, ⟨"GB10-TABLE-D244/raw-feature/45", .rawTrm⟩)
  | 46 => some (true, ⟨"GB10-TABLE-D244/raw-feature/46", .rawTrm⟩)
  | 47 => some (true, ⟨"GB10-TABLE-D244/raw-feature/47", .rawTrm⟩)
  | 48 => some (true, ⟨"GB10-TABLE-D244/raw-feature/48", .rawTrm⟩)
  | 49 => some (true, ⟨"GB10-TABLE-D244/raw-feature/49", .rawTrm⟩)
  | 50 => some (true, ⟨"GB10-TABLE-D244/raw-feature/50", .rawTrm⟩)
  | 51 => some (true, ⟨"GB10-TABLE-D244/raw-feature/51", .rawTrm⟩)
  | 52 => some (true, ⟨"GB10-TABLE-D244/raw-feature/52", .rawTrm⟩)
  | 53 => some (true, ⟨"GB10-TABLE-D244/raw-feature/53", .rawTrm⟩)
  | 54 => some (true, ⟨"GB10-TABLE-D244/raw-feature/54", .rawTrm⟩)
  | 55 => some (true, ⟨"GB10-TABLE-D244/raw-feature/55", .rawTrm⟩)
  | 56 => some (false, ⟨"GB10-TABLE-D244/raw-feature/56", .rawTrm⟩)
  | 57 => some (false, ⟨"GB10-TABLE-D244/raw-feature/57", .rawTrm⟩)
  | 58 => some (false, ⟨"GB10-TABLE-D244/raw-feature/58", .rawTrm⟩)
  | 60 => some (true, ⟨"GB10-TABLE-D244/raw-feature/60", .rawTrm⟩)
  | 61 => some (true, ⟨"GB10-TABLE-D244/raw-feature/61", .rawTrm⟩)
  | 63 => some (false, ⟨"GB10-TABLE-D244/raw-feature/63", .rawTrm⟩)
  | 64 => some (false, ⟨"GB10-TABLE-D244/raw-feature/64", .rawTrm⟩)
  | 65 => some (true, ⟨"GB10-TABLE-D244/raw-feature/65", .rawTrm⟩)
  | 66 => some (true, ⟨"GB10-TABLE-D244/raw-feature/66", .rawTrm⟩)
  | 67 => some (true, ⟨"GB10-TABLE-D244/raw-feature/67", .rawTrm⟩)
  | 68 => some (true, ⟨"GB10-TABLE-D244/raw-feature/68", .rawTrm⟩)
  | 69 => some (false, ⟨"GB10-TABLE-D244/raw-feature/69", .rawTrm⟩)
  | 70 => some (false, ⟨"GB10-TABLE-D244/raw-feature/70", .rawTrm⟩)
  | 71 => some (false, ⟨"GB10-TABLE-D244/raw-feature/71", .rawTrm⟩)
  | 72 => some (true, ⟨"GB10-TABLE-D244/raw-feature/72", .rawTrm⟩)
  | 73 => some (true, ⟨"GB10-TABLE-D244/raw-feature/73", .rawTrm⟩)
  | 74 => some (true, ⟨"GB10-TABLE-D244/raw-feature/74", .rawTrm⟩)
  | 75 => some (true, ⟨"GB10-TABLE-D244/raw-feature/75", .rawTrm⟩)
  | 76 => some (true, ⟨"GB10-TABLE-D244/raw-feature/76", .conditionalTrm⟩)
  | 77 => some (true, ⟨"GB10-TABLE-D244/raw-feature/77", .conditionalTrm⟩)
  | 78 => some (true, ⟨"GB10-TABLE-D244/raw-feature/78", .conditionalTrm⟩)
  | 79 => some (true, ⟨"GB10-TABLE-D244/raw-feature/79", .conditionalTrm⟩)
  | 81 => some (true, ⟨"GB10-TABLE-D244/raw-feature/81", .rawTrm⟩)
  | 82 => some (true, ⟨"GB10-TABLE-D244/raw-feature/82", .rawTrm⟩)
  | 83 => some (true, ⟨"GB10-TABLE-D244/raw-feature/83", .rawTrm⟩)
  | 84 => some (false, ⟨"GB10-TABLE-D244/raw-feature/84", .rawTrm⟩)
  | 85 => some (true, ⟨"GB10-TABLE-D244/raw-feature/85", .rawTrm⟩)
  | 86 => some (true, ⟨"GB10-TABLE-D244/raw-feature/86", .rawTrm⟩)
  | 87 => some (true, ⟨"GB10-TABLE-D244/raw-feature/87", .rawTrm⟩)
  | 88 => some (false, ⟨"GB10-TABLE-D244/raw-feature/88", .rawTrm⟩)
  | 89 => some (true, ⟨"GB10-TABLE-D244/raw-feature/89", .rawTrm⟩)
  | 90 => some (true, ⟨"GB10-TABLE-D244/raw-feature/90", .rawTrm⟩)
  | 91 => some (true, ⟨"GB10-TABLE-D244/raw-feature/91", .rawTrm⟩)
  | 92 => some (true, ⟨"GB10-TABLE-D244/raw-feature/92", .rawTrm⟩)
  | 93 => some (true, ⟨"GB10-TABLE-D244/raw-feature/93", .rawTrm⟩)
  | 94 => some (false, ⟨"GB10-TABLE-D244/raw-feature/94", .rawTrm⟩)
  | 95 => some (false, ⟨"GB10-TABLE-D244/raw-feature/95", .rawTrm⟩)
  | 96 => some (true, ⟨"GB10-TABLE-D244/raw-feature/96", .rawTrm⟩)
  | 97 => some (false, ⟨"GB10-TABLE-D244/raw-feature/97", .rawTrm⟩)
  | 98 => some (true, ⟨"GB10-TABLE-D244/raw-feature/98", .rawTrm⟩)
  | 100 => some (true, ⟨"GB10-TABLE-D244/raw-feature/100", .rawTrm⟩)
  | 101 => some (true, ⟨"GB10-TABLE-D244/raw-feature/101", .rawTrm⟩)
  | 103 => some (true, ⟨"GB10-TABLE-D244/raw-feature/103", .rawTrm⟩)
  | 104 => some (true, ⟨"GB10-TABLE-D244/raw-feature/104", .rawTrm⟩)
  | 105 => some (true, ⟨"GB10-TABLE-D244/raw-feature/105", .rawTrm⟩)
  | 106 => some (true, ⟨"GB10-TABLE-D244/raw-feature/106", .rawTrm⟩)
  | 107 => some (true, ⟨"GB10-TABLE-D244/raw-feature/107", .rawTrm⟩)
  | 108 => some (true, ⟨"GB10-TABLE-D244/raw-feature/108", .rawTrm⟩)
  | 109 => some (true, ⟨"GB10-TABLE-D244/raw-feature/109", .rawTrm⟩)
  | 110 => some (true, ⟨"GB10-TABLE-D244/raw-feature/110", .rawTrm⟩)
  | 111 => some (true, ⟨"GB10-TABLE-D244/raw-feature/111", .rawTrm⟩)
  | 112 => some (false, ⟨"GB10-TABLE-D244/raw-feature/112", .rawTrm⟩)
  | 113 => some (true, ⟨"GB10-TABLE-D244/raw-feature/113", .rawTrm⟩)
  | 115 => some (true, ⟨"GB10-TABLE-D244/raw-feature/115", .rawTrm⟩)
  | 116 => some (true, ⟨"GB10-TABLE-D244/raw-feature/116", .rawTrm⟩)
  | 117 => some (true, ⟨"GB10-TABLE-D244/raw-feature/117", .rawTrm⟩)
  | 118 => some (true, ⟨"GB10-TABLE-D244/raw-feature/118", .rawTrm⟩)
  | 119 => some (true, ⟨"GB10-TABLE-D244/raw-feature/119", .rawTrm⟩)
  | 120 => some (true, ⟨"GB10-TABLE-D244/raw-feature/120", .rawTrm⟩)
  | 121 => some (true, ⟨"GB10-TABLE-D244/raw-feature/121", .rawTrm⟩)
  | 122 => some (true, ⟨"GB10-TABLE-D244/raw-feature/122", .rawTrm⟩)
  | 123 => some (true, ⟨"GB10-TABLE-D244/raw-feature/123", .rawTrm⟩)
  | 124 => some (true, ⟨"GB10-TABLE-D244/raw-feature/124", .rawTrm⟩)
  | 125 => some (true, ⟨"GB10-TABLE-D244/raw-feature/125", .rawTrm⟩)
  | 126 => some (true, ⟨"GB10-TABLE-D244/raw-feature/126", .rawTrm⟩)
  | 127 => some (true, ⟨"GB10-TABLE-D244/raw-feature/127", .rawTrm⟩)
  | 128 => some (true, ⟨"GB10-TABLE-D244/raw-feature/128", .rawTrm⟩)
  | 129 => some (false, ⟨"GB10-TABLE-D244/raw-feature/129", .rawTrm⟩)
  | 130 => some (true, ⟨"GB10-TABLE-D244/raw-feature/130", .rawTrm⟩)
  | 131 => some (true, ⟨"GB10-TABLE-D244/raw-feature/131", .rawTrm⟩)
  | 132 => some (true, ⟨"GB10-TABLE-D244/raw-feature/132", .rawTrm⟩)
  | 133 => some (true, ⟨"GB10-TABLE-D244/raw-feature/133", .rawTrm⟩)
  | 135 => some (true, ⟨"GB10-TABLE-D244/raw-feature/135", .rawTrm⟩)
  | 136 => some (false, ⟨"GB10-TABLE-D244/raw-feature/136", .rawTrm⟩)
  | 137 => some (false, ⟨"GB10-TABLE-D244/raw-feature/137", .rawTrm⟩)
  | 138 => some (true, ⟨"GB10-TABLE-D244/raw-feature/138", .rawTrm⟩)
  | 139 => some (true, ⟨"GB10-TABLE-D244/raw-feature/139", .rawTrm⟩)
  | 140 => some (true, ⟨"GB10-TABLE-D244/raw-feature/140", .rawTrm⟩)
  | 141 => some (true, ⟨"GB10-TABLE-D244/raw-feature/141", .rawTrm⟩)
  | 142 => some (false, ⟨"GB10-TABLE-D244/raw-feature/142", .rawTrm⟩)
  | 143 => some (true, ⟨"GB10-TABLE-D244/raw-feature/143", .rawTrm⟩)
  | 144 => some (true, ⟨"GB10-TABLE-D244/raw-feature/144", .rawTrm⟩)
  | 145 => some (true, ⟨"GB10-TABLE-D244/raw-feature/145", .rawTrm⟩)
  | 146 => some (true, ⟨"GB10-TABLE-D244/raw-feature/146", .rawTrm⟩)
  | 147 => some (true, ⟨"GB10-TABLE-D244/raw-feature/147", .rawTrm⟩)
  | 148 => some (false, ⟨"GB10-TABLE-D244/raw-feature/148", .rawTrm⟩)
  | 149 => some (true, ⟨"GB10-TABLE-D244/raw-feature/149", .rawTrm⟩)
  | 150 => some (false, ⟨"GB10-TABLE-D244/raw-feature/150", .rawTrm⟩)
  | 151 => some (true, ⟨"GB10-TABLE-D244/raw-feature/151", .rawTrm⟩)
  | 152 => some (false, ⟨"GB10-TABLE-D244/raw-feature/152", .rawTrm⟩)
  | 153 => some (true, ⟨"GB10-TABLE-D244/raw-feature/153", .rawTrm⟩)
  | 154 => some (false, ⟨"GB10-TABLE-D244/raw-feature/154", .rawTrm⟩)
  | 155 => some (true, ⟨"GB10-TABLE-D244/raw-feature/155", .rawTrm⟩)
  | 156 => some (false, ⟨"GB10-TABLE-D244/raw-feature/156", .rawTrm⟩)
  | 157 => some (false, ⟨"GB10-TABLE-D244/raw-feature/157", .rawTrm⟩)
  | 158 => some (false, ⟨"GB10-TABLE-D244/raw-feature/158", .rawTrm⟩)
  | 159 => some (false, ⟨"GB10-TABLE-D244/raw-feature/159", .rawTrm⟩)
  | 161 => some (true, ⟨"GB10-TABLE-D244/raw-feature/161", .rawTrm⟩)
  | 162 => some (true, ⟨"GB10-TABLE-D244/raw-feature/162", .rawTrm⟩)
  | 163 => some (false, ⟨"GB10-TABLE-D244/raw-feature/163", .rawTrm⟩)
  | 165 => some (true, ⟨"GB10-TABLE-D244/raw-feature/165", .rawTrm⟩)
  | 166 => some (true, ⟨"GB10-TABLE-D244/raw-feature/166", .rawTrm⟩)
  | 167 => some (false, ⟨"GB10-TABLE-D244/raw-feature/167", .rawTrm⟩)
  | 168 => some (false, ⟨"GB10-TABLE-D244/raw-feature/168", .rawTrm⟩)
  | 170 => some (false, ⟨"GB10-TABLE-D244/raw-feature/170", .rawTrm⟩)
  | 171 => some (false, ⟨"GB10-TABLE-D244/raw-feature/171", .rawTrm⟩)
  | 172 => some (false, ⟨"GB10-TABLE-D244/raw-feature/172", .rawTrm⟩)
  | 174 => some (false, ⟨"GB10-TABLE-D244/raw-feature/174", .rawTrm⟩)
  | 175 => some (false, ⟨"GB10-TABLE-D244/raw-feature/175", .rawTrm⟩)
  | 177 => some (false, ⟨"GB10-TABLE-D244/raw-feature/177", .rawTrm⟩)
  | 178 => some (false, ⟨"GB10-TRM/x925:25156=0b0000,ArmARM-RAZ/a725:ID_AA64MMFR3_EL1.TCRX", .rawTrm⟩)
  | 179 => some (false, ⟨"GB10-TABLE-D244/raw-feature/179", .rawTrm⟩)
  | 181 => some (false, ⟨"GB10-TRM/x925:25122=0b0000,ArmARM-RAZ/a725:ID_AA64MMFR3_EL1.AIE", .rawTrm⟩)
  | 185 => some (false, ⟨"GB10-TABLE-D244/raw-feature/185", .rawTrm⟩)
  | 187 => some (true, ⟨"GB10-TABLE-D244/raw-feature/187", .rawTrm⟩)
  | 188 => some (false, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:24573,a725:25021/ID_AA64MMFR0_EL1.FGT=0b0001", .rawTrm⟩)
  | 189 => some (false, ⟨"GB10-TRM/x925:24804,a725:25256/ID_AA64MMFR1_EL1.HAFDBS=0b0010", .rawTrm⟩)
  | 190 => some (false, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:24252,a725:24738/ID_AA64ISAR1_EL1.LRCPC=0b0010", .rawTrm⟩)
  | 200 => some (false, ⟨"GB10-TABLE-D244/raw-feature/200", .rawTrm⟩)
  | 204 => some (false, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:23552,a725:24083/ID_AA64DFR0_EL1.PMUVer=0b0111", .rawTrm⟩)
  | 207 => some (false, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:22973,a725:23577/ID_AA64PFR0_EL1.RAS=0b0010", .rawTrm⟩)
  | 209 => some (false, ⟨"GB10-TRM/x925:25148=0b0000,ArmARM-RAZ/a725:ID_AA64MMFR3_EL1.S1PIE", .rawTrm⟩)
  | 210 => some (false, ⟨"GB10-TRM/x925:25141=0b0000,ArmARM-RAZ/a725:ID_AA64MMFR3_EL1.S1POE", .rawTrm⟩)
  | 213 => some (false, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:24219,a725:24720/ID_AA64ISAR1_EL1.SPECRES=0b0001", .rawTrm⟩)
  | 216 => some (false, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:23526,a725:24051/ID_AA64DFR0_EL1.PMSVer=0b0011", .rawTrm⟩)
  | 218 => some (false, ⟨"GB10-TRM/x925:23137=0b0000,a725:23711=RES0/ID_AA64PFR1_EL1.THE", .rawTrm⟩)
  | 219 => some (true, ⟨"GB10-TABLE-D244/raw-feature/219", .rawTrm⟩)
  | 220 => some (true, ⟨"GB10-TABLE-D244/raw-feature/220", .rawTrm⟩)
  | 221 => some (true, ⟨"GB10-TABLE-D244/raw-feature/221", .rawTrm⟩)
  | 222 => some (true, ⟨"GB10-TABLE-D244/raw-feature/222", .conditionalTrm⟩)
  | 223 => some (true, ⟨"GB10-TABLE-D244/raw-feature/223", .rawTrm⟩)
  | 224 => some (true, ⟨"GB10-TABLE-D244/raw-feature/224", .conditionalTrm⟩)
  | 225 => some (true, ⟨"GB10-TABLE-D244/raw-feature/225", .conditionalTrm⟩)
  | 226 => some (true, ⟨"GB10-TABLE-D244/raw-feature/226", .conditionalTrm⟩)
  | 227 => some (false, ⟨"GB10-TABLE-D244/raw-feature/227", .rawTrm⟩)
  | 228 => some (true, ⟨"GB10-TABLE-D244/raw-feature/228", .rawTrm⟩)
  | 229 => some (true, ⟨"GB10-TABLE-D244/raw-feature/229", .rawTrm⟩)
  | 230 => some (false, ⟨"GB10-TABLE-D244/raw-feature/230", .rawTrm⟩)
  | 231 => some (false, ⟨"GB10-TABLE-D244/raw-feature/231", .rawTrm⟩)
  | 232 => some (false, ⟨"GB10-TABLE-D244/raw-feature/232", .rawTrm⟩)
  | 233 => some (false, ⟨"GB10-TABLE-D244/raw-feature/233", .rawTrm⟩)
  | 234 => some (false, ⟨"GB10-TABLE-D244/raw-feature/234", .rawTrm⟩)
  | 235 => some (false, ⟨"GB10-TABLE-D244/raw-feature/235", .rawTrm⟩)
  | 236 => some (false, ⟨"GB10-TABLE-D244/raw-feature/236", .rawTrm⟩)
  | 237 => some (false, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:23498,a725:24033/ID_AA64DFR0_EL1.BRBE=0b0000", .rawTrm⟩)
  | 239 => some (false, ⟨"GB10-TABLE-D244/raw-feature/239", .rawTrm⟩)
  | 242 => some (false, ⟨"GB10-TRM/x925:25115=0b0000,ArmARM-RAZ/a725:ID_AA64MMFR3_EL1.D128", .rawTrm⟩)
  | 245 => some (false, ⟨"GB10-TABLE-D244/raw-feature/245", .rawTrm⟩)
  | 247 => some (false, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:24041,a725:24539/ID_AA64ISAR0_EL1.Atomic=0b0010", .rawTrm⟩)
  | 248 => some (false, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:24953,a725:25412/ID_AA64MMFR2_EL1.VARange=0b0000", .rawTrm⟩)
  | 250 => some (false, ⟨"GB10-TABLE-D244/raw-feature/250", .rawTrm⟩)
  | 251 => some (false, ⟨"GB10-TABLE-D244/raw-feature/251", .rawTrm⟩)
  | 252 => some (false, ⟨"GB10-TRM-DOUG-20261112T2135Z/x925:23401,a725:23923/ID_AA64ZFR0_EL1.SVEver=0b0001", .rawTrm⟩)
  | _ => none

#check "CURRENT_DECL FeatureSource.bankAlias"
/-- The named boolean banks are aliases, never independent feature choices. -/
def bankAlias : ArmFull.Bank_Bool → Option (Fin 259)
  | .FEAT_AA32EL0_IMPLEMENTED => some ⟨0, by decide⟩
  | .FEAT_AA32EL1_IMPLEMENTED => some ⟨1, by decide⟩
  | .FEAT_AA32EL2_IMPLEMENTED => some ⟨2, by decide⟩
  | .FEAT_AA32EL3_IMPLEMENTED => some ⟨3, by decide⟩
  | .FEAT_AA64EL0_IMPLEMENTED => some ⟨4, by decide⟩
  | .FEAT_AA64EL1_IMPLEMENTED => some ⟨5, by decide⟩
  | .FEAT_AA64EL2_IMPLEMENTED => some ⟨6, by decide⟩
  | .FEAT_AA64EL3_IMPLEMENTED => some ⟨7, by decide⟩
  | .FEAT_EL0_IMPLEMENTED => some ⟨8, by decide⟩
  | .FEAT_EL1_IMPLEMENTED => some ⟨9, by decide⟩
  | .FEAT_EL2_IMPLEMENTED => some ⟨10, by decide⟩
  | .FEAT_EL3_IMPLEMENTED => some ⟨11, by decide⟩
  | .FEAT_AES_IMPLEMENTED => some ⟨12, by decide⟩
  | .FEAT_AdvSIMD_IMPLEMENTED => some ⟨13, by decide⟩
  | .FEAT_CSV2_1p1_IMPLEMENTED => some ⟨14, by decide⟩
  | .FEAT_CSV2_1p2_IMPLEMENTED => some ⟨15, by decide⟩
  | .FEAT_CSV2_2_IMPLEMENTED => some ⟨16, by decide⟩
  | .FEAT_CSV2_3_IMPLEMENTED => some ⟨17, by decide⟩
  | .FEAT_DoubleLock_IMPLEMENTED => some ⟨18, by decide⟩
  | .FEAT_ETMv4_IMPLEMENTED => some ⟨19, by decide⟩
  | .FEAT_ETMv4p1_IMPLEMENTED => some ⟨20, by decide⟩
  | .FEAT_ETMv4p2_IMPLEMENTED => some ⟨21, by decide⟩
  | .FEAT_ETMv4p3_IMPLEMENTED => some ⟨22, by decide⟩
  | .FEAT_ETMv4p4_IMPLEMENTED => some ⟨23, by decide⟩
  | .FEAT_ETMv4p5_IMPLEMENTED => some ⟨24, by decide⟩
  | .FEAT_ETMv4p6_IMPLEMENTED => some ⟨25, by decide⟩
  | .FEAT_ETS2_IMPLEMENTED => some ⟨26, by decide⟩
  | .FEAT_FP_IMPLEMENTED => some ⟨27, by decide⟩
  | .FEAT_GICv3_IMPLEMENTED => some ⟨28, by decide⟩
  | .FEAT_GICv3_LEGACY_IMPLEMENTED => some ⟨29, by decide⟩
  | .FEAT_GICv3_TDIR_IMPLEMENTED => some ⟨30, by decide⟩
  | .FEAT_GICv3p1_IMPLEMENTED => some ⟨31, by decide⟩
  | .FEAT_GICv4_IMPLEMENTED => some ⟨32, by decide⟩
  | .FEAT_GICv4p1_IMPLEMENTED => some ⟨33, by decide⟩
  | .FEAT_IVIPT_IMPLEMENTED => some ⟨34, by decide⟩
  | .FEAT_PCSRv8_IMPLEMENTED => some ⟨35, by decide⟩
  | .FEAT_PMULL_IMPLEMENTED => some ⟨36, by decide⟩
  | .FEAT_PMUv3_IMPLEMENTED => some ⟨37, by decide⟩
  | .FEAT_PMUv3_EXT_IMPLEMENTED => some ⟨38, by decide⟩
  | .FEAT_PMUv3_EXT32_IMPLEMENTED => some ⟨39, by decide⟩
  | .FEAT_SHA1_IMPLEMENTED => some ⟨40, by decide⟩
  | .FEAT_SHA256_IMPLEMENTED => some ⟨41, by decide⟩
  | .FEAT_TRC_EXT_IMPLEMENTED => some ⟨42, by decide⟩
  | .FEAT_TRC_SR_IMPLEMENTED => some ⟨43, by decide⟩
  | .FEAT_nTLBPA_IMPLEMENTED => some ⟨44, by decide⟩
  | .FEAT_CRC32_IMPLEMENTED => some ⟨45, by decide⟩
  | .FEAT_Debugv8p1_IMPLEMENTED => some ⟨46, by decide⟩
  | .FEAT_HAFDBS_IMPLEMENTED => some ⟨47, by decide⟩
  | .FEAT_HPDS_IMPLEMENTED => some ⟨48, by decide⟩
  | .FEAT_LOR_IMPLEMENTED => some ⟨49, by decide⟩
  | .FEAT_LSE_IMPLEMENTED => some ⟨50, by decide⟩
  | .FEAT_PAN_IMPLEMENTED => some ⟨51, by decide⟩
  | .FEAT_PMUv3p1_IMPLEMENTED => some ⟨52, by decide⟩
  | .FEAT_RDM_IMPLEMENTED => some ⟨53, by decide⟩
  | .FEAT_VHE_IMPLEMENTED => some ⟨54, by decide⟩
  | .FEAT_VMID16_IMPLEMENTED => some ⟨55, by decide⟩
  | .FEAT_AA32BF16_IMPLEMENTED => some ⟨56, by decide⟩
  | .FEAT_AA32HPD_IMPLEMENTED => some ⟨57, by decide⟩
  | .FEAT_AA32I8MM_IMPLEMENTED => some ⟨58, by decide⟩
  | .FEAT_ASMv8p2_IMPLEMENTED => some ⟨59, by decide⟩
  | .FEAT_DPB_IMPLEMENTED => some ⟨60, by decide⟩
  | .FEAT_Debugv8p2_IMPLEMENTED => some ⟨61, by decide⟩
  | .FEAT_EDHSR_IMPLEMENTED => some ⟨62, by decide⟩
  | .FEAT_F32MM_IMPLEMENTED => some ⟨63, by decide⟩
  | .FEAT_F64MM_IMPLEMENTED => some ⟨64, by decide⟩
  | .FEAT_FP16_IMPLEMENTED => some ⟨65, by decide⟩
  | .FEAT_HPDS2_IMPLEMENTED => some ⟨66, by decide⟩
  | .FEAT_I8MM_IMPLEMENTED => some ⟨67, by decide⟩
  | .FEAT_IESB_IMPLEMENTED => some ⟨68, by decide⟩
  | .FEAT_LPA_IMPLEMENTED => some ⟨69, by decide⟩
  | .FEAT_LSMAOC_IMPLEMENTED => some ⟨70, by decide⟩
  | .FEAT_LVA_IMPLEMENTED => some ⟨71, by decide⟩
  | .FEAT_MPAM_IMPLEMENTED => some ⟨72, by decide⟩
  | .FEAT_PAN2_IMPLEMENTED => some ⟨73, by decide⟩
  | .FEAT_PCSRv8p2_IMPLEMENTED => some ⟨74, by decide⟩
  | .FEAT_RAS_IMPLEMENTED => some ⟨75, by decide⟩
  | .FEAT_SHA3_IMPLEMENTED => some ⟨76, by decide⟩
  | .FEAT_SHA512_IMPLEMENTED => some ⟨77, by decide⟩
  | .FEAT_SM3_IMPLEMENTED => some ⟨78, by decide⟩
  | .FEAT_SM4_IMPLEMENTED => some ⟨79, by decide⟩
  | .FEAT_SPE_IMPLEMENTED => some ⟨80, by decide⟩
  | .FEAT_SVE_IMPLEMENTED => some ⟨81, by decide⟩
  | .FEAT_TTCNP_IMPLEMENTED => some ⟨82, by decide⟩
  | .FEAT_UAO_IMPLEMENTED => some ⟨83, by decide⟩
  | .FEAT_VPIPT_IMPLEMENTED => some ⟨84, by decide⟩
  | .FEAT_XNX_IMPLEMENTED => some ⟨85, by decide⟩
  | .FEAT_CCIDX_IMPLEMENTED => some ⟨86, by decide⟩
  | .FEAT_CONSTPACFIELD_IMPLEMENTED => some ⟨87, by decide⟩
  | .FEAT_EPAC_IMPLEMENTED => some ⟨88, by decide⟩
  | .FEAT_FCMA_IMPLEMENTED => some ⟨89, by decide⟩
  | .FEAT_FPAC_IMPLEMENTED => some ⟨90, by decide⟩
  | .FEAT_FPACCOMBINE_IMPLEMENTED => some ⟨91, by decide⟩
  | .FEAT_JSCVT_IMPLEMENTED => some ⟨92, by decide⟩
  | .FEAT_LRCPC_IMPLEMENTED => some ⟨93, by decide⟩
  | .FEAT_NV_IMPLEMENTED => some ⟨94, by decide⟩
  | .FEAT_PACIMP_IMPLEMENTED => some ⟨95, by decide⟩
  | .FEAT_PACQARMA3_IMPLEMENTED => some ⟨96, by decide⟩
  | .FEAT_PACQARMA5_IMPLEMENTED => some ⟨97, by decide⟩
  | .FEAT_PAuth_IMPLEMENTED => some ⟨98, by decide⟩
  | .FEAT_SPEv1p1_IMPLEMENTED => some ⟨99, by decide⟩
  | .FEAT_AMUv1_IMPLEMENTED => some ⟨100, by decide⟩
  | .FEAT_BBM_IMPLEMENTED => some ⟨101, by decide⟩
  | .FEAT_CNTSC_IMPLEMENTED => some ⟨102, by decide⟩
  | .FEAT_DIT_IMPLEMENTED => some ⟨103, by decide⟩
  | .FEAT_Debugv8p4_IMPLEMENTED => some ⟨104, by decide⟩
  | .FEAT_DotProd_IMPLEMENTED => some ⟨105, by decide⟩
  | .FEAT_DoubleFault_IMPLEMENTED => some ⟨106, by decide⟩
  | .FEAT_FHM_IMPLEMENTED => some ⟨107, by decide⟩
  | .FEAT_FlagM_IMPLEMENTED => some ⟨108, by decide⟩
  | .FEAT_IDST_IMPLEMENTED => some ⟨109, by decide⟩
  | .FEAT_LRCPC2_IMPLEMENTED => some ⟨110, by decide⟩
  | .FEAT_LSE2_IMPLEMENTED => some ⟨111, by decide⟩
  | .FEAT_NV2_IMPLEMENTED => some ⟨112, by decide⟩
  | .FEAT_PMUv3p4_IMPLEMENTED => some ⟨113, by decide⟩
  | .FEAT_RASSAv1p1_IMPLEMENTED => some ⟨114, by decide⟩
  | .FEAT_RASv1p1_IMPLEMENTED => some ⟨115, by decide⟩
  | .FEAT_S2FWB_IMPLEMENTED => some ⟨116, by decide⟩
  | .FEAT_SEL2_IMPLEMENTED => some ⟨117, by decide⟩
  | .FEAT_TLBIOS_IMPLEMENTED => some ⟨118, by decide⟩
  | .FEAT_TLBIRANGE_IMPLEMENTED => some ⟨119, by decide⟩
  | .FEAT_TRF_IMPLEMENTED => some ⟨120, by decide⟩
  | .FEAT_TTL_IMPLEMENTED => some ⟨121, by decide⟩
  | .FEAT_TTST_IMPLEMENTED => some ⟨122, by decide⟩
  | .FEAT_BTI_IMPLEMENTED => some ⟨123, by decide⟩
  | .FEAT_CSV2_IMPLEMENTED => some ⟨124, by decide⟩
  | .FEAT_CSV3_IMPLEMENTED => some ⟨125, by decide⟩
  | .FEAT_DPB2_IMPLEMENTED => some ⟨126, by decide⟩
  | .FEAT_E0PD_IMPLEMENTED => some ⟨127, by decide⟩
  | .FEAT_EVT_IMPLEMENTED => some ⟨128, by decide⟩
  | .FEAT_ExS_IMPLEMENTED => some ⟨129, by decide⟩
  | .FEAT_FRINTTS_IMPLEMENTED => some ⟨130, by decide⟩
  | .FEAT_FlagM2_IMPLEMENTED => some ⟨131, by decide⟩
  | .FEAT_GTG_IMPLEMENTED => some ⟨132, by decide⟩
  | .FEAT_MTE_IMPLEMENTED => some ⟨133, by decide⟩
  | .FEAT_MTE2_IMPLEMENTED => some ⟨134, by decide⟩
  | .FEAT_PMUv3p5_IMPLEMENTED => some ⟨135, by decide⟩
  | .FEAT_RNG_IMPLEMENTED => some ⟨136, by decide⟩
  | .FEAT_RNG_TRAP_IMPLEMENTED => some ⟨137, by decide⟩
  | .FEAT_SB_IMPLEMENTED => some ⟨138, by decide⟩
  | .FEAT_SPECRES_IMPLEMENTED => some ⟨139, by decide⟩
  | .FEAT_SSBS_IMPLEMENTED => some ⟨140, by decide⟩
  | .FEAT_SSBS2_IMPLEMENTED => some ⟨141, by decide⟩
  | .FEAT_AMUv1p1_IMPLEMENTED => some ⟨142, by decide⟩
  | .FEAT_BF16_IMPLEMENTED => some ⟨143, by decide⟩
  | .FEAT_DGH_IMPLEMENTED => some ⟨144, by decide⟩
  | .FEAT_ECV_IMPLEMENTED => some ⟨145, by decide⟩
  | .FEAT_FGT_IMPLEMENTED => some ⟨146, by decide⟩
  | .FEAT_HPMN0_IMPLEMENTED => some ⟨147, by decide⟩
  | .FEAT_MPAMv0p1_IMPLEMENTED => some ⟨148, by decide⟩
  | .FEAT_MPAMv1p1_IMPLEMENTED => some ⟨149, by decide⟩
  | .FEAT_MTPMU_IMPLEMENTED => some ⟨150, by decide⟩
  | .FEAT_PAuth2_IMPLEMENTED => some ⟨151, by decide⟩
  | .FEAT_TWED_IMPLEMENTED => some ⟨152, by decide⟩
  | .FEAT_AFP_IMPLEMENTED => some ⟨153, by decide⟩
  | .FEAT_EBF16_IMPLEMENTED => some ⟨154, by decide⟩
  | .FEAT_HCX_IMPLEMENTED => some ⟨155, by decide⟩
  | .FEAT_LPA2_IMPLEMENTED => some ⟨156, by decide⟩
  | .FEAT_LS64_IMPLEMENTED => some ⟨157, by decide⟩
  | .FEAT_LS64_ACCDATA_IMPLEMENTED => some ⟨158, by decide⟩
  | .FEAT_LS64_V_IMPLEMENTED => some ⟨159, by decide⟩
  | .FEAT_MTE3_IMPLEMENTED => some ⟨160, by decide⟩
  | .FEAT_PAN3_IMPLEMENTED => some ⟨161, by decide⟩
  | .FEAT_PMUv3p7_IMPLEMENTED => some ⟨162, by decide⟩
  | .FEAT_RPRES_IMPLEMENTED => some ⟨163, by decide⟩
  | .FEAT_SPEv1p2_IMPLEMENTED => some ⟨164, by decide⟩
  | .FEAT_WFxT_IMPLEMENTED => some ⟨165, by decide⟩
  | .FEAT_XS_IMPLEMENTED => some ⟨166, by decide⟩
  | .FEAT_CMOW_IMPLEMENTED => some ⟨167, by decide⟩
  | .FEAT_Debugv8p8_IMPLEMENTED => some ⟨168, by decide⟩
  | .FEAT_GICv3_NMI_IMPLEMENTED => some ⟨169, by decide⟩
  | .FEAT_HBC_IMPLEMENTED => some ⟨170, by decide⟩
  | .FEAT_MOPS_IMPLEMENTED => some ⟨171, by decide⟩
  | .FEAT_NMI_IMPLEMENTED => some ⟨172, by decide⟩
  | .FEAT_PMUv3_EXT64_IMPLEMENTED => some ⟨173, by decide⟩
  | .FEAT_PMUv3_TH_IMPLEMENTED => some ⟨174, by decide⟩
  | .FEAT_PMUv3p8_IMPLEMENTED => some ⟨175, by decide⟩
  | .FEAT_SCTLR2_IMPLEMENTED => some ⟨176, by decide⟩
  | .FEAT_SPEv1p3_IMPLEMENTED => some ⟨177, by decide⟩
  | .FEAT_TCR2_IMPLEMENTED => some ⟨178, by decide⟩
  | .FEAT_TIDCP1_IMPLEMENTED => some ⟨179, by decide⟩
  | .FEAT_ADERR_IMPLEMENTED => some ⟨180, by decide⟩
  | .FEAT_AIE_IMPLEMENTED => some ⟨181, by decide⟩
  | .FEAT_ANERR_IMPLEMENTED => some ⟨182, by decide⟩
  | .FEAT_CLRBHB_IMPLEMENTED => some ⟨183, by decide⟩
  | .FEAT_CSSC_IMPLEMENTED => some ⟨184, by decide⟩
  | .FEAT_Debugv8p9_IMPLEMENTED => some ⟨185, by decide⟩
  | .FEAT_DoubleFault2_IMPLEMENTED => some ⟨186, by decide⟩
  | .FEAT_ECBHB_IMPLEMENTED => some ⟨187, by decide⟩
  | .FEAT_FGT2_IMPLEMENTED => some ⟨188, by decide⟩
  | .FEAT_HAFT_IMPLEMENTED => some ⟨189, by decide⟩
  | .FEAT_LRCPC3_IMPLEMENTED => some ⟨190, by decide⟩
  | .FEAT_MTE4_IMPLEMENTED => some ⟨191, by decide⟩
  | .FEAT_MTE_ASYM_FAULT_IMPLEMENTED => some ⟨192, by decide⟩
  | .FEAT_MTE_ASYNC_IMPLEMENTED => some ⟨193, by decide⟩
  | .FEAT_MTE_CANONICAL_TAGS_IMPLEMENTED => some ⟨194, by decide⟩
  | .FEAT_MTE_NO_ADDRESS_TAGS_IMPLEMENTED => some ⟨195, by decide⟩
  | .FEAT_MTE_PERM_IMPLEMENTED => some ⟨196, by decide⟩
  | .FEAT_MTE_STORE_ONLY_IMPLEMENTED => some ⟨197, by decide⟩
  | .FEAT_MTE_TAGGED_FAR_IMPLEMENTED => some ⟨198, by decide⟩
  | .FEAT_PCSRv8p9_IMPLEMENTED => some ⟨199, by decide⟩
  | .FEAT_PFAR_IMPLEMENTED => some ⟨200, by decide⟩
  | .FEAT_PMUv3_EDGE_IMPLEMENTED => some ⟨201, by decide⟩
  | .FEAT_PMUv3_ICNTR_IMPLEMENTED => some ⟨202, by decide⟩
  | .FEAT_PMUv3_SS_IMPLEMENTED => some ⟨203, by decide⟩
  | .FEAT_PMUv3p9_IMPLEMENTED => some ⟨204, by decide⟩
  | .FEAT_PRFMSLC_IMPLEMENTED => some ⟨205, by decide⟩
  | .FEAT_RASSAv2_IMPLEMENTED => some ⟨206, by decide⟩
  | .FEAT_RASv2_IMPLEMENTED => some ⟨207, by decide⟩
  | .FEAT_RPRFM_IMPLEMENTED => some ⟨208, by decide⟩
  | .FEAT_S1PIE_IMPLEMENTED => some ⟨209, by decide⟩
  | .FEAT_S1POE_IMPLEMENTED => some ⟨210, by decide⟩
  | .FEAT_S2PIE_IMPLEMENTED => some ⟨211, by decide⟩
  | .FEAT_S2POE_IMPLEMENTED => some ⟨212, by decide⟩
  | .FEAT_SPECRES2_IMPLEMENTED => some ⟨213, by decide⟩
  | .FEAT_SPE_CRR_IMPLEMENTED => some ⟨214, by decide⟩
  | .FEAT_SPE_FDS_IMPLEMENTED => some ⟨215, by decide⟩
  | .FEAT_SPEv1p4_IMPLEMENTED => some ⟨216, by decide⟩
  | .FEAT_SPMU_IMPLEMENTED => some ⟨217, by decide⟩
  | .FEAT_THE_IMPLEMENTED => some ⟨218, by decide⟩
  | .FEAT_DoPD_IMPLEMENTED => some ⟨219, by decide⟩
  | .FEAT_ETE_IMPLEMENTED => some ⟨220, by decide⟩
  | .FEAT_SVE2_IMPLEMENTED => some ⟨221, by decide⟩
  | .FEAT_SVE_AES_IMPLEMENTED => some ⟨222, by decide⟩
  | .FEAT_SVE_BitPerm_IMPLEMENTED => some ⟨223, by decide⟩
  | .FEAT_SVE_PMULL128_IMPLEMENTED => some ⟨224, by decide⟩
  | .FEAT_SVE_SHA3_IMPLEMENTED => some ⟨225, by decide⟩
  | .FEAT_SVE_SM4_IMPLEMENTED => some ⟨226, by decide⟩
  | .FEAT_TME_IMPLEMENTED => some ⟨227, by decide⟩
  | .FEAT_TRBE_IMPLEMENTED => some ⟨228, by decide⟩
  | .FEAT_ETEv1p1_IMPLEMENTED => some ⟨229, by decide⟩
  | .FEAT_BRBE_IMPLEMENTED => some ⟨230, by decide⟩
  | .FEAT_ETEv1p2_IMPLEMENTED => some ⟨231, by decide⟩
  | .FEAT_RME_IMPLEMENTED => some ⟨232, by decide⟩
  | .FEAT_SME_IMPLEMENTED => some ⟨233, by decide⟩
  | .FEAT_SME_F64F64_IMPLEMENTED => some ⟨234, by decide⟩
  | .FEAT_SME_FA64_IMPLEMENTED => some ⟨235, by decide⟩
  | .FEAT_SME_I16I64_IMPLEMENTED => some ⟨236, by decide⟩
  | .FEAT_BRBEv1p1_IMPLEMENTED => some ⟨237, by decide⟩
  | .FEAT_MEC_IMPLEMENTED => some ⟨238, by decide⟩
  | .FEAT_SME2_IMPLEMENTED => some ⟨239, by decide⟩
  | .FEAT_ABLE_IMPLEMENTED => some ⟨240, by decide⟩
  | .FEAT_CHK_IMPLEMENTED => some ⟨241, by decide⟩
  | .FEAT_D128_IMPLEMENTED => some ⟨242, by decide⟩
  | .FEAT_EBEP_IMPLEMENTED => some ⟨243, by decide⟩
  | .FEAT_ETEv1p3_IMPLEMENTED => some ⟨244, by decide⟩
  | .FEAT_GCS_IMPLEMENTED => some ⟨245, by decide⟩
  | .FEAT_ITE_IMPLEMENTED => some ⟨246, by decide⟩
  | .FEAT_LSE128_IMPLEMENTED => some ⟨247, by decide⟩
  | .FEAT_LVA3_IMPLEMENTED => some ⟨248, by decide⟩
  | .FEAT_SEBEP_IMPLEMENTED => some ⟨249, by decide⟩
  | .FEAT_SME2p1_IMPLEMENTED => some ⟨250, by decide⟩
  | .FEAT_SME_F16F16_IMPLEMENTED => some ⟨251, by decide⟩
  | .FEAT_SVE2p1_IMPLEMENTED => some ⟨252, by decide⟩
  | .FEAT_SVE_B16B16_IMPLEMENTED => some ⟨253, by decide⟩
  | .FEAT_SYSINSTR128_IMPLEMENTED => some ⟨254, by decide⟩
  | .FEAT_SYSREG128_IMPLEMENTED => some ⟨255, by decide⟩
  | .FEAT_TRBE_EXT_IMPLEMENTED => some ⟨256, by decide⟩
  | .FEAT_TRBE_MPAM_IMPLEMENTED => some ⟨257, by decide⟩
  | _ => none

/-- One fixed recipe value; unresolved slots are inputs, never seed defaults. -/
def recipe (index : Fin 259) : Slot Bool :=
  match declared index with
  | some (value, authority) => .literal value authority
  | none => .unresolved ("raw.FeatureImpl." ++ toString index.val)

theorem recipe_no_caller (index : Fin 259) : Slot.isCaller (recipe index) = false := by
  unfold recipe
  split <;> rfl

abbrev Unknowns := UnknownValues recipe

private def noCaller : CallerValues recipe := fun index impossible =>
  False.elim (Bool.false_ne_true ((recipe_no_caller index).symm.trans impossible))

def value (unknowns : Unknowns) (index : Fin 259) : Bool :=
  interpret recipe unknowns noCaller index

#check "CURRENT_DECL FeatureSource.Configuration"
/-- The kernel equality fixes the complete feature vector to this recipe and these unknowns. -/
structure Configuration (unknowns : Unknowns) where
  private mk ::
  vector : Vector Bool 259
  canonical : vector = Vector.ofFn (value unknowns)

namespace Configuration

def ofSource (unknowns : Unknowns) : Configuration unknowns :=
  ⟨Vector.ofFn (value unknowns), rfl⟩

theorem coordinate_exact {unknowns : Unknowns} (configuration : Configuration unknowns)
    (index : Fin 259) : configuration.vector[index] = value unknowns index := by
  rw [configuration.canonical]
  simp

theorem configuration_exact {unknowns : Unknowns} (configuration : Configuration unknowns) :
    configuration = ofSource unknowns := by
  cases configuration
  rename_i vector canonical
  unfold ofSource
  congr 1

end Configuration

/-- Mathematical agreement with both raw feature views at the SAME actual entry. -/
def AgreesAt {unknowns : Unknowns} (configuration : Configuration unknowns)
    (regs : ArmFull.Regs) : Prop :=
  regs.FeatureImpl = configuration.vector ∧
    ∀ bank index, bankAlias bank = some index →
      regs.bank_Bool bank = configuration.vector[index]

theorem agrees_feature {unknowns : Unknowns} (configuration : Configuration unknowns)
    (regs : ArmFull.Regs) (agreement : AgreesAt configuration regs) (index : Fin 259) :
    regs.FeatureImpl[index] = value unknowns index := by
  exact (congrArg (fun vector : Vector Bool 259 => vector[index]) agreement.1).trans
    (Configuration.coordinate_exact configuration index)

theorem agrees_bank {unknowns : Unknowns} (configuration : Configuration unknowns)
    (regs : ArmFull.Regs) (agreement : AgreesAt configuration regs)
    (bank : ArmFull.Bank_Bool) (index : Fin 259) (alias : bankAlias bank = some index) :
    regs.bank_Bool bank = value unknowns index := by
  exact (agreement.2 bank index alias).trans
    (Configuration.coordinate_exact configuration index)

theorem value_declared (unknowns : Unknowns) (index : Fin 259)
    (expected : Bool) (authority : AuthorityRef)
    (record : declared index = some (expected, authority)) :
    value unknowns index = expected := by
  apply interpret_literal recipe unknowns noCaller index expected authority
  simp only [recipe, record]

theorem value_unresolved (unknowns : Unknowns) (index : Fin 259)
    (record : declared index = none) :
    value unknowns index = unknowns index (by simp only [recipe, record, Slot.isUnknown]) := by
  apply interpret_unknown recipe unknowns noCaller index
    ("raw.FeatureImpl." ++ toString index.val)
  simp only [recipe, record]

/-- A positive mathematical consistency witness, never the valuation of an actual invocation. -/
theorem unknown_domain_nonempty : Nonempty Unknowns :=
  ⟨fun _ _ => false⟩

/-- Every outer valuation has a canonical feature vector; no hardware evidence is produced. -/
theorem uniform_vector_exists (unknowns : Unknowns) :
    ∃ vector : Vector Bool 259, ∀ index : Fin 259, vector[index] = value unknowns index := by
  exact ⟨(Configuration.ofSource unknowns).vector,
    fun index => Configuration.coordinate_exact (Configuration.ofSource unknowns) index⟩

end ReleaseProfile.GB10.FeatureSource

#print axioms ReleaseProfile.GB10.FeatureSource.Configuration.coordinate_exact
#print axioms ReleaseProfile.GB10.FeatureSource.Configuration.configuration_exact
#print axioms ReleaseProfile.GB10.FeatureSource.agrees_feature
#print axioms ReleaseProfile.GB10.FeatureSource.agrees_bank
#print axioms ReleaseProfile.GB10.FeatureSource.value_declared
#print axioms ReleaseProfile.GB10.FeatureSource.value_unresolved
#print axioms ReleaseProfile.GB10.FeatureSource.unknown_domain_nonempty
#print axioms ReleaseProfile.GB10.FeatureSource.uniform_vector_exists
