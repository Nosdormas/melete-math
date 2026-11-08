module

public import DsrgRank.DSRG

/-!
Gives explicit adjacency matrices of DSRGs with parameters (6, 2, 1, 0, 1), (6, 3, 2, 1, 2), (8, 3,
2, 1, 1), (10, 4, 2, 1, 2) and (18, 4, 3, 0, 1), proves that each satisfies IsDSRG, and proves that
a modified matrix for each of them fails the conditions.
-/

@[expose] public section

namespace DsrgRank.Graphs.Small

open DsrgRank

theorem g_6_2_1_0_1_0 : IsDSRG 6 (ofBitmasks [6, 17, 40, 17, 40, 6]) 2 1 0 1 := by
  decide +kernel

theorem g_6_2_1_0_1_0_switched : ¬ IsDSRG 6 (ofBitmasks [18, 5, 40, 17, 40, 6]) 2 1 0 1 := by
  decide +kernel

theorem g_6_3_2_1_2_1 : IsDSRG 6 (ofBitmasks [14, 13, 49, 50, 37, 26]) 3 2 1 2 := by
  decide +kernel

theorem g_6_3_2_1_2_1_switched : ¬ IsDSRG 6 (ofBitmasks [28, 13, 35, 50, 37, 26]) 3 2 1 2 := by
  decide +kernel

theorem g_8_3_2_1_1_2 : IsDSRG 8 (ofBitmasks [14, 13, 81, 162, 69, 138, 176, 112]) 3 2 1 1 := by
  decide +kernel

theorem g_8_3_2_1_1_2_switched : ¬ IsDSRG 8 (ofBitmasks [28, 13, 67, 162, 69, 138, 176, 112]) 3 2 1 1 := by
  decide +kernel

theorem g_10_4_2_1_2_1 : IsDSRG 10 (ofBitmasks [396, 792, 561, 99, 198, 594, 165, 330, 660, 297]) 4 2 1 2 := by
  decide +kernel

theorem g_10_4_2_1_2_1_switched : ¬ IsDSRG 10 (ofBitmasks [408, 780, 561, 99, 198, 594, 165, 330, 660, 297]) 4 2 1 2 := by
  decide +kernel

theorem g_18_4_3_0_1_1 : IsDSRG 18 (ofBitmasks [586, 2340, 1169, 36881, 147492, 73738, 139393, 69892, 49218, 82945, 43012, 135682, 10376, 17504, 4880, 66824, 131744, 34896]) 4 3 0 1 := by
  decide +kernel

theorem g_18_4_3_0_1_1_switched : ¬ IsDSRG 18 (ofBitmasks [582, 2344, 1169, 36881, 147492, 73738, 139393, 69892, 49218, 82945, 43012, 135682, 10376, 17504, 4880, 66824, 131744, 34896]) 4 3 0 1 := by
  decide +kernel

end DsrgRank.Graphs.Small
