import Sunproj.Triple.Data.T000
import Sunproj.Triple.Data.T001
import Sunproj.Triple.Data.T002
import Sunproj.Triple.Data.T003
import Sunproj.Triple.Data.T004
import Sunproj.Triple.Data.T005
import Sunproj.Triple.Data.T006
import Sunproj.Triple.Data.T007
import Sunproj.Triple.Data.T008
import Sunproj.Triple.Data.T009
import Sunproj.Triple.Data.T010
import Sunproj.Triple.Data.T011
import Sunproj.Triple.Data.T012
import Sunproj.Triple.Data.T013
import Sunproj.Triple.Data.T014
import Sunproj.Triple.Data.T015
import Sunproj.Triple.Data.T016
import Sunproj.Triple.Data.T017
import Sunproj.Triple.Data.T018
import Sunproj.Triple.Data.T019
import Sunproj.Triple.Data.T020
import Sunproj.Triple.Data.T021
import Sunproj.Triple.Data.T022
import Sunproj.Triple.Data.T023
import Sunproj.Triple.Data.T024
import Sunproj.Triple.Data.T025
import Sunproj.Triple.Data.T026
import Sunproj.Triple.Data.T027
import Sunproj.Triple.Data.T028
import Sunproj.Triple.Data.T029
import Sunproj.Triple.Data.T030
import Sunproj.Triple.Data.T031
import Sunproj.Triple.Data.T032
import Sunproj.Triple.Data.T033
import Sunproj.Triple.Data.T034
import Sunproj.Triple.Data.T035
import Sunproj.Triple.Data.T036
import Sunproj.Triple.Data.T037
import Sunproj.Triple.Data.T038
import Sunproj.Triple.Data.T039
import Sunproj.Triple.Data.T040
import Sunproj.Triple.Data.T041
import Sunproj.Triple.Data.T042
import Sunproj.Triple.Data.T043
import Sunproj.Triple.Data.T044
import Sunproj.Triple.Data.T045
import Sunproj.Triple.Data.T046
import Sunproj.Triple.Data.T047
import Sunproj.Triple.Data.T048
import Sunproj.Triple.Data.T049
import Sunproj.Triple.Data.T050
import Sunproj.Triple.Data.T051
import Sunproj.Triple.Data.T052
import Sunproj.Triple.Data.T053
import Sunproj.Triple.Data.T054
import Sunproj.Triple.Data.T055
import Sunproj.Triple.Data.T056
import Sunproj.Triple.Data.T057
import Sunproj.Triple.Data.T058
import Sunproj.Triple.Data.T059
import Sunproj.Triple.Data.T060
import Sunproj.Triple.Data.T061
import Sunproj.Triple.Data.T062
import Sunproj.Triple.Data.T063
import Sunproj.Triple.Data.T064
import Sunproj.Triple.Data.T065
import Sunproj.Triple.Data.T066
import Sunproj.Triple.Data.T067
import Sunproj.Triple.Data.T068
import Sunproj.Triple.Data.T069
import Sunproj.Triple.Data.T070
import Sunproj.Triple.Data.T071
import Sunproj.Triple.Data.T072
import Sunproj.Triple.Data.T073
import Sunproj.Triple.Data.T074
import Sunproj.Triple.Data.T075
import Sunproj.Triple.Data.T076
import Sunproj.Triple.Data.T077
import Sunproj.Triple.Data.T078
import Sunproj.Triple.Data.T079
import Sunproj.Triple.Data.T080
import Sunproj.Triple.Data.T081
import Sunproj.Triple.Data.T082
import Sunproj.Triple.Data.T083
import Sunproj.Triple.Data.T084
import Sunproj.Triple.Data.T085
import Sunproj.Triple.Data.T086
import Sunproj.Triple.Data.T087
import Sunproj.Triple.Data.T088
import Sunproj.Triple.Data.T089
import Sunproj.Triple.Data.T090
import Sunproj.Triple.Data.T091
import Sunproj.Triple.Data.T092
import Sunproj.Triple.Data.T093
import Sunproj.Triple.Data.T094
import Sunproj.Triple.Data.T095
import Sunproj.Triple.Data.T096
import Sunproj.Triple.Data.T097
import Sunproj.Triple.Data.T098
import Sunproj.Triple.Data.T099
import Sunproj.Triple.Data.T100
import Sunproj.Triple.Data.T101
import Sunproj.Triple.Data.T102

/-! Chains the member chunks (generated). -/

namespace Triple

lemma chain {a b lo hi c : ℕ} (ha : a ≤ Nat.count IsT lo)
    (h : Nat.count IsT lo + c ≤ Nat.count IsT hi) (hb : b = a + c) : b ≤ Nat.count IsT hi := by
  omega

/-- At least 77055 members are `≤ 148770907`. -/
theorem count_le : 77055 ≤ Nat.count IsT 148770908 := by
  have h0 : 750 ≤ Nat.count IsT 400244 := chain (Nat.zero_le _) DT000_count rfl
  have h1 : 1500 ≤ Nat.count IsT 1048124 := chain h0 DT001_count rfl
  have h2 : 2250 ≤ Nat.count IsT 1718288 := chain h1 DT002_count rfl
  have h3 : 3000 ≤ Nat.count IsT 2555168 := chain h2 DT003_count rfl
  have h4 : 3750 ≤ Nat.count IsT 3412064 := chain h3 DT004_count rfl
  have h5 : 4500 ≤ Nat.count IsT 4353494 := chain h4 DT005_count rfl
  have h6 : 5250 ≤ Nat.count IsT 5327894 := chain h5 DT006_count rfl
  have h7 : 6000 ≤ Nat.count IsT 6298724 := chain h6 DT007_count rfl
  have h8 : 6750 ≤ Nat.count IsT 7293068 := chain h7 DT008_count rfl
  have h9 : 7500 ≤ Nat.count IsT 8340848 := chain h8 DT009_count rfl
  have h10 : 8250 ≤ Nat.count IsT 9403184 := chain h9 DT010_count rfl
  have h11 : 9000 ≤ Nat.count IsT 10509464 := chain h10 DT011_count rfl
  have h12 : 9750 ≤ Nat.count IsT 11616344 := chain h11 DT012_count rfl
  have h13 : 10500 ≤ Nat.count IsT 12727004 := chain h12 DT013_count rfl
  have h14 : 11250 ≤ Nat.count IsT 13880594 := chain h13 DT014_count rfl
  have h15 : 12000 ≤ Nat.count IsT 14996474 := chain h14 DT015_count rfl
  have h16 : 12750 ≤ Nat.count IsT 16230854 := chain h15 DT016_count rfl
  have h17 : 13500 ≤ Nat.count IsT 17464634 := chain h16 DT017_count rfl
  have h18 : 14250 ≤ Nat.count IsT 18698678 := chain h17 DT018_count rfl
  have h19 : 15000 ≤ Nat.count IsT 19967444 := chain h18 DT019_count rfl
  have h20 : 15750 ≤ Nat.count IsT 21144548 := chain h19 DT020_count rfl
  have h21 : 16500 ≤ Nat.count IsT 22438568 := chain h20 DT021_count rfl
  have h22 : 17250 ≤ Nat.count IsT 23673578 := chain h21 DT022_count rfl
  have h23 : 18000 ≤ Nat.count IsT 24923024 := chain h22 DT023_count rfl
  have h24 : 18750 ≤ Nat.count IsT 26294138 := chain h23 DT024_count rfl
  have h25 : 19500 ≤ Nat.count IsT 27605108 := chain h24 DT025_count rfl
  have h26 : 20250 ≤ Nat.count IsT 28882874 := chain h25 DT026_count rfl
  have h27 : 21000 ≤ Nat.count IsT 30217928 := chain h26 DT027_count rfl
  have h28 : 21750 ≤ Nat.count IsT 31625774 := chain h27 DT028_count rfl
  have h29 : 22500 ≤ Nat.count IsT 32941718 := chain h28 DT029_count rfl
  have h30 : 23250 ≤ Nat.count IsT 34366094 := chain h29 DT030_count rfl
  have h31 : 24000 ≤ Nat.count IsT 35720408 := chain h30 DT031_count rfl
  have h32 : 24750 ≤ Nat.count IsT 37085558 := chain h31 DT032_count rfl
  have h33 : 25500 ≤ Nat.count IsT 38472608 := chain h32 DT033_count rfl
  have h34 : 26250 ≤ Nat.count IsT 39843998 := chain h33 DT034_count rfl
  have h35 : 27000 ≤ Nat.count IsT 41282078 := chain h34 DT035_count rfl
  have h36 : 27750 ≤ Nat.count IsT 42736538 := chain h35 DT036_count rfl
  have h37 : 28500 ≤ Nat.count IsT 44219798 := chain h36 DT037_count rfl
  have h38 : 29250 ≤ Nat.count IsT 45657878 := chain h37 DT038_count rfl
  have h39 : 30000 ≤ Nat.count IsT 47093324 := chain h38 DT039_count rfl
  have h40 : 30750 ≤ Nat.count IsT 48611468 := chain h39 DT040_count rfl
  have h41 : 31500 ≤ Nat.count IsT 50099474 := chain h40 DT041_count rfl
  have h42 : 32250 ≤ Nat.count IsT 51633734 := chain h41 DT042_count rfl
  have h43 : 33000 ≤ Nat.count IsT 53143214 := chain h42 DT043_count rfl
  have h44 : 33750 ≤ Nat.count IsT 54595268 := chain h43 DT044_count rfl
  have h45 : 34500 ≤ Nat.count IsT 56117684 := chain h44 DT045_count rfl
  have h46 : 35250 ≤ Nat.count IsT 57609158 := chain h45 DT046_count rfl
  have h47 : 36000 ≤ Nat.count IsT 59078444 := chain h46 DT047_count rfl
  have h48 : 36750 ≤ Nat.count IsT 60564068 := chain h47 DT048_count rfl
  have h49 : 37500 ≤ Nat.count IsT 61975004 := chain h48 DT049_count rfl
  have h50 : 38250 ≤ Nat.count IsT 63524474 := chain h49 DT050_count rfl
  have h51 : 39000 ≤ Nat.count IsT 65025968 := chain h50 DT051_count rfl
  have h52 : 39750 ≤ Nat.count IsT 66698474 := chain h51 DT052_count rfl
  have h53 : 40500 ≤ Nat.count IsT 68168918 := chain h52 DT053_count rfl
  have h54 : 41250 ≤ Nat.count IsT 69669008 := chain h53 DT054_count rfl
  have h55 : 42000 ≤ Nat.count IsT 71235584 := chain h54 DT055_count rfl
  have h56 : 42750 ≤ Nat.count IsT 72735068 := chain h55 DT056_count rfl
  have h57 : 43500 ≤ Nat.count IsT 74317844 := chain h56 DT057_count rfl
  have h58 : 44250 ≤ Nat.count IsT 75894668 := chain h57 DT058_count rfl
  have h59 : 45000 ≤ Nat.count IsT 77488988 := chain h58 DT059_count rfl
  have h60 : 45750 ≤ Nat.count IsT 79055438 := chain h59 DT060_count rfl
  have h61 : 46500 ≤ Nat.count IsT 80650478 := chain h60 DT061_count rfl
  have h62 : 47250 ≤ Nat.count IsT 82155038 := chain h61 DT062_count rfl
  have h63 : 48000 ≤ Nat.count IsT 83749448 := chain h62 DT063_count rfl
  have h64 : 48750 ≤ Nat.count IsT 85326464 := chain h63 DT064_count rfl
  have h65 : 49500 ≤ Nat.count IsT 86863628 := chain h64 DT065_count rfl
  have h66 : 50250 ≤ Nat.count IsT 88420664 := chain h65 DT066_count rfl
  have h67 : 51000 ≤ Nat.count IsT 90048818 := chain h66 DT067_count rfl
  have h68 : 51750 ≤ Nat.count IsT 91756658 := chain h67 DT068_count rfl
  have h69 : 52500 ≤ Nat.count IsT 93444518 := chain h68 DT069_count rfl
  have h70 : 53250 ≤ Nat.count IsT 95090924 := chain h69 DT070_count rfl
  have h71 : 54000 ≤ Nat.count IsT 96608648 := chain h70 DT071_count rfl
  have h72 : 54750 ≤ Nat.count IsT 98209298 := chain h71 DT072_count rfl
  have h73 : 55500 ≤ Nat.count IsT 99890384 := chain h72 DT073_count rfl
  have h74 : 56250 ≤ Nat.count IsT 101613074 := chain h73 DT074_count rfl
  have h75 : 57000 ≤ Nat.count IsT 103216508 := chain h74 DT075_count rfl
  have h76 : 57750 ≤ Nat.count IsT 104759534 := chain h75 DT076_count rfl
  have h77 : 58500 ≤ Nat.count IsT 106343354 := chain h76 DT077_count rfl
  have h78 : 59250 ≤ Nat.count IsT 108015878 := chain h77 DT078_count rfl
  have h79 : 60000 ≤ Nat.count IsT 109645868 := chain h78 DT079_count rfl
  have h80 : 60750 ≤ Nat.count IsT 111285914 := chain h79 DT080_count rfl
  have h81 : 61500 ≤ Nat.count IsT 112997324 := chain h80 DT081_count rfl
  have h82 : 62250 ≤ Nat.count IsT 114712394 := chain h81 DT082_count rfl
  have h83 : 63000 ≤ Nat.count IsT 116357408 := chain h82 DT083_count rfl
  have h84 : 63750 ≤ Nat.count IsT 117974318 := chain h83 DT084_count rfl
  have h85 : 64500 ≤ Nat.count IsT 119722454 := chain h84 DT085_count rfl
  have h86 : 65250 ≤ Nat.count IsT 121401734 := chain h85 DT086_count rfl
  have h87 : 66000 ≤ Nat.count IsT 123094508 := chain h86 DT087_count rfl
  have h88 : 66750 ≤ Nat.count IsT 124738298 := chain h87 DT088_count rfl
  have h89 : 67500 ≤ Nat.count IsT 126465944 := chain h88 DT089_count rfl
  have h90 : 68250 ≤ Nat.count IsT 128128784 := chain h89 DT090_count rfl
  have h91 : 69000 ≤ Nat.count IsT 129787244 := chain h90 DT091_count rfl
  have h92 : 69750 ≤ Nat.count IsT 131544224 := chain h91 DT092_count rfl
  have h93 : 70500 ≤ Nat.count IsT 133321814 := chain h92 DT093_count rfl
  have h94 : 71250 ≤ Nat.count IsT 135101384 := chain h93 DT094_count rfl
  have h95 : 72000 ≤ Nat.count IsT 136826528 := chain h94 DT095_count rfl
  have h96 : 72750 ≤ Nat.count IsT 138583478 := chain h95 DT096_count rfl
  have h97 : 73500 ≤ Nat.count IsT 140386484 := chain h96 DT097_count rfl
  have h98 : 74250 ≤ Nat.count IsT 142172198 := chain h97 DT098_count rfl
  have h99 : 75000 ≤ Nat.count IsT 143999264 := chain h98 DT099_count rfl
  have h100 : 75750 ≤ Nat.count IsT 145759178 := chain h99 DT100_count rfl
  have h101 : 76500 ≤ Nat.count IsT 147470468 := chain h100 DT101_count rfl
  have h102 : 77055 ≤ Nat.count IsT 148770908 := chain h101 DT102_count rfl
  exact h102

end Triple
