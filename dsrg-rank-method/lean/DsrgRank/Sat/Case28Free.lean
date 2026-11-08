module

public import DsrgRank.Sat.Subset
public import DsrgRank.Sat.TrieCheck

/-!
Stores the clauses and a refutation of one CNF formula for parameters (28, 6, 3, 2, 1).
formula_unsat checks the refutation with the trie checker, and unsat_of_superset shows that every
clause set containing this formula is unsatisfiable.
-/

@[expose] public section

-- formula: lib/mu_one_sat.py, mode free, (28, 6, 3, 2, 1) (checks/dsrg28_check.py)
-- certificate: certificates/free-28-6-3-2-1.lrat.xz (checks/dsrg28_certificate.py)
-- cnf_sha256 = 4b59a3ff8959ed54f9a0a5ae2ca02ef07d41eb126fb759610f6732b9daf04ce3
-- vars = 131518
-- clauses = 300889
-- lrat_sha256 = 7771e5ec55282d9da62937af8687057900f28c8a9cef03cc166c4e7abda0ed21
-- lrat_steps = 525
-- core_clauses = 1627
-- check = kernel

namespace DsrgRank.Sat.Case28Free

open Std.Sat Std.Tactic.BVDecide.LRAT

set_option maxRecDepth 1000000

def clauses : List (List (Nat × Bool)) := [
  [(307, false), (738, true)], -- 1274
  [(586, false), (738, false), (740, true)], -- 1276
  [(587, false), (740, false), (742, true)], -- 1278
  [(588, false), (742, false), (744, true)], -- 1280
  [(589, false), (744, false), (746, true)], -- 1282
  [(590, false), (746, false), (748, true)], -- 1284
  [(748, false), (749, true)], -- 1285
  [(749, false), (755, true)], -- 1298
  [(755, false), (761, true)], -- 1311
  [(761, false), (767, true)], -- 1324
  [(594, false), (761, false)], -- 1325
  [(767, false), (773, true)], -- 1337
  [(595, false), (767, false)], -- 1338
  [(773, false), (779, true)], -- 1350
  [(596, false), (773, false)], -- 1351
  [(779, false), (785, true)], -- 1363
  [(597, false), (779, false)], -- 1364
  [(785, false), (791, true)], -- 1376
  [(598, false), (785, false)], -- 1377
  [(791, false), (797, true)], -- 1389
  [(599, false), (791, false)], -- 1390
  [(797, false), (803, true)], -- 1402
  [(600, false), (797, false)], -- 1403
  [(803, false), (809, true)], -- 1415
  [(601, false), (803, false)], -- 1416
  [(809, false), (815, true)], -- 1428
  [(602, false), (809, false)], -- 1429
  [(815, false), (821, true)], -- 1441
  [(603, false), (815, false)], -- 1442
  [(821, false), (827, true)], -- 1454
  [(604, false), (821, false)], -- 1455
  [(827, false), (833, true)], -- 1467
  [(605, false), (827, false)], -- 1468
  [(833, false), (839, true)], -- 1480
  [(606, false), (833, false)], -- 1481
  [(839, false), (845, true)], -- 1493
  [(607, false), (839, false)], -- 1494
  [(845, false), (851, true)], -- 1506
  [(608, false), (845, false)], -- 1507
  [(851, false), (857, true)], -- 1519
  [(609, false), (851, false)], -- 1520
  [(857, false), (863, true)], -- 1532
  [(610, false), (857, false)], -- 1533
  [(611, false), (863, false)], -- 1540
  [(308, false), (1293, true)], -- 2282
  [(864, false), (1293, false), (1295, true)], -- 2284
  [(1142, false), (1295, false), (1297, true)], -- 2286
  [(1143, false), (1297, false), (1299, true)], -- 2288
  [(1144, false), (1299, false), (1301, true)], -- 2290
  [(1145, false), (1301, false), (1303, true)], -- 2292
  [(1303, false), (1304, true)], -- 2293
  [(1304, false), (1310, true)], -- 2306
  [(1310, false), (1316, true)], -- 2319
  [(1316, false), (1322, true)], -- 2332
  [(1149, false), (1316, false)], -- 2333
  [(1322, false), (1328, true)], -- 2345
  [(1150, false), (1322, false)], -- 2346
  [(1328, false), (1334, true)], -- 2358
  [(1151, false), (1328, false)], -- 2359
  [(1334, false), (1340, true)], -- 2371
  [(1152, false), (1334, false)], -- 2372
  [(1340, false), (1346, true)], -- 2384
  [(1153, false), (1340, false)], -- 2385
  [(1346, false), (1352, true)], -- 2397
  [(1154, false), (1346, false)], -- 2398
  [(1352, false), (1358, true)], -- 2410
  [(1155, false), (1352, false)], -- 2411
  [(1358, false), (1364, true)], -- 2423
  [(1156, false), (1358, false)], -- 2424
  [(1364, false), (1370, true)], -- 2436
  [(1157, false), (1364, false)], -- 2437
  [(1370, false), (1376, true)], -- 2449
  [(1158, false), (1370, false)], -- 2450
  [(1376, false), (1382, true)], -- 2462
  [(1159, false), (1376, false)], -- 2463
  [(1382, false), (1388, true)], -- 2475
  [(1160, false), (1382, false)], -- 2476
  [(1388, false), (1394, true)], -- 2488
  [(1161, false), (1388, false)], -- 2489
  [(1394, false), (1400, true)], -- 2501
  [(1162, false), (1394, false)], -- 2502
  [(1400, false), (1406, true)], -- 2514
  [(1163, false), (1400, false)], -- 2515
  [(1406, false), (1412, true)], -- 2527
  [(1164, false), (1406, false)], -- 2528
  [(1412, false), (1418, true)], -- 2540
  [(1165, false), (1412, false)], -- 2541
  [(1166, false), (1418, false)], -- 2548
  [(309, false), (1846, true)], -- 3290
  [(865, false), (1846, false), (1848, true)], -- 3292
  [(1419, false), (1848, false), (1850, true)], -- 3294
  [(1696, false), (1850, false), (1852, true)], -- 3296
  [(1697, false), (1852, false), (1854, true)], -- 3298
  [(1698, false), (1854, false), (1856, true)], -- 3300
  [(1856, false), (1857, true)], -- 3301
  [(1699, false), (1856, false)], -- 3302
  [(1857, false), (1863, true)], -- 3314
  [(1700, false), (1857, false)], -- 3315
  [(1863, false), (1869, true)], -- 3327
  [(1701, false), (1863, false)], -- 3328
  [(1869, false), (1875, true)], -- 3340
  [(1702, false), (1869, false)], -- 3341
  [(1875, false), (1881, true)], -- 3353
  [(1703, false), (1875, false)], -- 3354
  [(1881, false), (1887, true)], -- 3366
  [(1704, false), (1881, false)], -- 3367
  [(1887, false), (1893, true)], -- 3379
  [(1705, false), (1887, false)], -- 3380
  [(1893, false), (1899, true)], -- 3392
  [(1706, false), (1893, false)], -- 3393
  [(1899, false), (1905, true)], -- 3405
  [(1707, false), (1899, false)], -- 3406
  [(1905, false), (1911, true)], -- 3418
  [(1708, false), (1905, false)], -- 3419
  [(1911, false), (1917, true)], -- 3431
  [(1709, false), (1911, false)], -- 3432
  [(1917, false), (1923, true)], -- 3444
  [(1710, false), (1917, false)], -- 3445
  [(1923, false), (1929, true)], -- 3457
  [(1711, false), (1923, false)], -- 3458
  [(1929, false), (1935, true)], -- 3470
  [(1712, false), (1929, false)], -- 3471
  [(1935, false), (1941, true)], -- 3483
  [(1713, false), (1935, false)], -- 3484
  [(1941, false), (1947, true)], -- 3496
  [(1714, false), (1941, false)], -- 3497
  [(1947, false), (1953, true)], -- 3509
  [(1715, false), (1947, false)], -- 3510
  [(1953, false), (1959, true)], -- 3522
  [(1716, false), (1953, false)], -- 3523
  [(1959, false), (1965, true)], -- 3535
  [(1717, false), (1959, false)], -- 3536
  [(1965, false), (1971, true)], -- 3548
  [(1718, false), (1965, false)], -- 3549
  [(1719, false), (1971, false)], -- 3556
  [(15067, false), (864, true)], -- 28623
  [(15067, true), (29, false), (864, false)], -- 28624
  [(15068, false), (865, true)], -- 28626
  [(15068, true), (30, false), (865, false)], -- 28627
  [(15069, false), (866, true)], -- 28629
  [(15069, true), (31, false), (866, false)], -- 28630
  [(15070, false), (867, true)], -- 28632
  [(15070, true), (32, false), (867, false)], -- 28633
  [(15071, false), (868, true)], -- 28635
  [(15071, true), (33, false), (868, false)], -- 28636
  [(15072, false), (34, true)], -- 28637
  [(15073, false), (35, true)], -- 28640
  [(15074, false), (36, true)], -- 28643
  [(15075, false), (37, true)], -- 28646
  [(15076, false), (38, true)], -- 28649
  [(15077, false), (39, true)], -- 28652
  [(15078, false), (40, true)], -- 28655
  [(15079, false), (41, true)], -- 28658
  [(15080, false), (42, true)], -- 28661
  [(15081, false), (43, true)], -- 28664
  [(15082, false), (44, true)], -- 28667
  [(15083, false), (45, true)], -- 28670
  [(15084, false), (46, true)], -- 28673
  [(15085, false), (47, true)], -- 28676
  [(15086, false), (48, true)], -- 28679
  [(15087, false), (49, true)], -- 28682
  [(15088, false), (50, true)], -- 28685
  [(15089, false), (51, true)], -- 28688
  [(15090, false), (52, true)], -- 28691
  [(15091, false), (53, true)], -- 28694
  [(15092, false), (54, true)], -- 28697
  [(15067, true), (15093, true), (28, false)], -- 28700
  [(15093, false), (15094, true), (28, false)], -- 28701
  [(15068, true), (15093, false), (15095, true), (28, false)], -- 28702
  [(15095, false), (15096, true), (28, false)], -- 28703
  [(15069, true), (15095, false), (15097, true), (28, false)], -- 28704
  [(15097, false), (15098, true), (28, false)], -- 28705
  [(15070, true), (15097, false), (15099, true), (28, false)], -- 28706
  [(15099, false), (15100, true), (28, false)], -- 28707
  [(15068, true), (15094, true), (28, false)], -- 28749
  [(15069, true), (15094, false), (15096, true), (28, false)], -- 28750
  [(15070, true), (15096, false), (15098, true), (28, false)], -- 28751
  [(15071, true), (15098, false), (15100, true), (28, false)], -- 28752
  [(15072, true), (15100, false), (15102, true), (28, false)], -- 28753
  [(15073, true), (15102, false), (15104, true), (28, false)], -- 28754
  [(15074, true), (15104, false), (15106, true), (28, false)], -- 28755
  [(15075, true), (15106, false), (15108, true), (28, false)], -- 28756
  [(15076, true), (15108, false), (15110, true), (28, false)], -- 28757
  [(15077, true), (15110, false), (15112, true), (28, false)], -- 28758
  [(15078, true), (15112, false), (15114, true), (28, false)], -- 28759
  [(15079, true), (15114, false), (15116, true), (28, false)], -- 28760
  [(15080, true), (15116, false), (15118, true), (28, false)], -- 28761
  [(15081, true), (15118, false), (15120, true), (28, false)], -- 28762
  [(15082, true), (15120, false), (15122, true), (28, false)], -- 28763
  [(15083, true), (15122, false), (15124, true), (28, false)], -- 28764
  [(15084, true), (15124, false), (15126, true), (28, false)], -- 28765
  [(15085, true), (15126, false), (15128, true), (28, false)], -- 28766
  [(15086, true), (15128, false), (15130, true), (28, false)], -- 28767
  [(15087, true), (15130, false), (15132, true), (28, false)], -- 28768
  [(15088, true), (15132, false), (15134, true), (28, false)], -- 28769
  [(15089, true), (15134, false), (15136, true), (28, false)], -- 28770
  [(15090, true), (15136, false), (15138, true), (28, false)], -- 28771
  [(15091, true), (15138, false), (15140, true), (28, false)], -- 28772
  [(15092, true), (15140, false), (28, false)], -- 28773
  [(15067, false), (15141, true), (28, false)], -- 28774
  [(15141, false), (15142, true), (28, false)], -- 28775
  [(15068, false), (15141, false), (15143, true), (28, false)], -- 28776
  [(15143, false), (15144, true), (28, false)], -- 28777
  [(15069, false), (15143, false), (28, false)], -- 28778
  [(15069, false), (15142, false), (15144, true), (28, false)], -- 28781
  [(15144, false), (15146, true), (28, false)], -- 28782
  [(15070, false), (15144, false), (28, false)], -- 28783
  [(15069, false), (15145, true), (28, false)], -- 28784
  [(15070, false), (15145, false), (15146, true), (28, false)], -- 28786
  [(15071, false), (15146, false), (28, false)], -- 28788
  [(15214, false), (586, true)], -- 28968
  [(15214, true), (28, false), (586, false)], -- 28969
  [(15215, false), (1419, true)], -- 28971
  [(15215, true), (30, false), (1419, false)], -- 28972
  [(15216, false), (1420, true)], -- 28974
  [(15216, true), (31, false), (1420, false)], -- 28975
  [(15217, false), (1421, true)], -- 28977
  [(15217, true), (32, false), (1421, false)], -- 28978
  [(15218, false), (1422, true)], -- 28980
  [(15218, true), (33, false), (1422, false)], -- 28981
  [(15219, false), (34, true)], -- 28982
  [(15220, false), (35, true)], -- 28985
  [(15221, false), (36, true)], -- 28988
  [(15222, false), (37, true)], -- 28991
  [(15223, false), (38, true)], -- 28994
  [(15224, false), (39, true)], -- 28997
  [(15225, false), (40, true)], -- 29000
  [(15226, false), (41, true)], -- 29003
  [(15227, false), (42, true)], -- 29006
  [(15228, false), (43, true)], -- 29009
  [(15229, false), (44, true)], -- 29012
  [(15230, false), (45, true)], -- 29015
  [(15231, false), (46, true)], -- 29018
  [(15232, false), (47, true)], -- 29021
  [(15233, false), (48, true)], -- 29024
  [(15234, false), (49, true)], -- 29027
  [(15235, false), (50, true)], -- 29030
  [(15236, false), (51, true)], -- 29033
  [(15237, false), (52, true)], -- 29036
  [(15238, false), (53, true)], -- 29039
  [(15239, false), (54, true)], -- 29042
  [(15214, true), (15240, true), (29, false)], -- 29045
  [(15240, false), (15241, true), (29, false)], -- 29046
  [(15215, true), (15240, false), (15242, true), (29, false)], -- 29047
  [(15242, false), (15243, true), (29, false)], -- 29048
  [(15216, true), (15242, false), (15244, true), (29, false)], -- 29049
  [(15244, false), (15245, true), (29, false)], -- 29050
  [(15217, true), (15244, false), (15246, true), (29, false)], -- 29051
  [(15246, false), (15247, true), (29, false)], -- 29052
  [(15215, true), (15241, true), (29, false)], -- 29094
  [(15216, true), (15241, false), (15243, true), (29, false)], -- 29095
  [(15217, true), (15243, false), (15245, true), (29, false)], -- 29096
  [(15218, true), (15245, false), (15247, true), (29, false)], -- 29097
  [(15219, true), (15247, false), (15249, true), (29, false)], -- 29098
  [(15220, true), (15249, false), (15251, true), (29, false)], -- 29099
  [(15221, true), (15251, false), (15253, true), (29, false)], -- 29100
  [(15222, true), (15253, false), (15255, true), (29, false)], -- 29101
  [(15223, true), (15255, false), (15257, true), (29, false)], -- 29102
  [(15224, true), (15257, false), (15259, true), (29, false)], -- 29103
  [(15225, true), (15259, false), (15261, true), (29, false)], -- 29104
  [(15226, true), (15261, false), (15263, true), (29, false)], -- 29105
  [(15227, true), (15263, false), (15265, true), (29, false)], -- 29106
  [(15228, true), (15265, false), (15267, true), (29, false)], -- 29107
  [(15229, true), (15267, false), (15269, true), (29, false)], -- 29108
  [(15230, true), (15269, false), (15271, true), (29, false)], -- 29109
  [(15231, true), (15271, false), (15273, true), (29, false)], -- 29110
  [(15232, true), (15273, false), (15275, true), (29, false)], -- 29111
  [(15233, true), (15275, false), (15277, true), (29, false)], -- 29112
  [(15234, true), (15277, false), (15279, true), (29, false)], -- 29113
  [(15235, true), (15279, false), (15281, true), (29, false)], -- 29114
  [(15236, true), (15281, false), (15283, true), (29, false)], -- 29115
  [(15237, true), (15283, false), (15285, true), (29, false)], -- 29116
  [(15238, true), (15285, false), (15287, true), (29, false)], -- 29117
  [(15239, true), (15287, false), (29, false)], -- 29118
  [(15214, false), (15288, true), (29, false)], -- 29119
  [(15215, false), (15288, false), (15290, true), (29, false)], -- 29121
  [(15290, false), (15291, true), (29, false)], -- 29122
  [(15216, false), (15290, false), (29, false)], -- 29123
  [(15215, false), (15289, true), (29, false)], -- 29124
  [(15216, false), (15289, false), (15291, true), (29, false)], -- 29126
  [(15291, false), (15293, true), (29, false)], -- 29127
  [(15217, false), (15291, false), (29, false)], -- 29128
  [(15216, false), (15292, true), (29, false)], -- 29129
  [(15217, false), (15292, false), (15293, true), (29, false)], -- 29131
  [(15218, false), (15293, false), (29, false)], -- 29133
  [(15361, false), (587, true)], -- 29313
  [(15361, true), (28, false), (587, false)], -- 29314
  [(15362, false), (1142, true)], -- 29316
  [(15362, true), (29, false), (1142, false)], -- 29317
  [(15363, false), (1972, true)], -- 29319
  [(15363, true), (31, false), (1972, false)], -- 29320
  [(15364, false), (1973, true)], -- 29322
  [(15364, true), (32, false), (1973, false)], -- 29323
  [(15365, false), (1974, true)], -- 29325
  [(15365, true), (33, false), (1974, false)], -- 29326
  [(15366, false), (34, true)], -- 29327
  [(15367, false), (35, true)], -- 29330
  [(15368, false), (36, true)], -- 29333
  [(15369, false), (37, true)], -- 29336
  [(15370, false), (38, true)], -- 29339
  [(15371, false), (39, true)], -- 29342
  [(15372, false), (40, true)], -- 29345
  [(15373, false), (41, true)], -- 29348
  [(15374, false), (42, true)], -- 29351
  [(15375, false), (43, true)], -- 29354
  [(15376, false), (44, true)], -- 29357
  [(15377, false), (45, true)], -- 29360
  [(15378, false), (46, true)], -- 29363
  [(15379, false), (47, true)], -- 29366
  [(15380, false), (48, true)], -- 29369
  [(15381, false), (49, true)], -- 29372
  [(15382, false), (50, true)], -- 29375
  [(15383, false), (51, true)], -- 29378
  [(15384, false), (52, true)], -- 29381
  [(15385, false), (53, true)], -- 29384
  [(15386, false), (54, true)], -- 29387
  [(15361, true), (15387, true), (30, false)], -- 29390
  [(15387, false), (15388, true), (30, false)], -- 29391
  [(15362, true), (15387, false), (15389, true), (30, false)], -- 29392
  [(15389, false), (15390, true), (30, false)], -- 29393
  [(15363, true), (15389, false), (15391, true), (30, false)], -- 29394
  [(15391, false), (15392, true), (30, false)], -- 29395
  [(15364, true), (15391, false), (15393, true), (30, false)], -- 29396
  [(15393, false), (15394, true), (30, false)], -- 29397
  [(15362, true), (15388, true), (30, false)], -- 29439
  [(15363, true), (15388, false), (15390, true), (30, false)], -- 29440
  [(15364, true), (15390, false), (15392, true), (30, false)], -- 29441
  [(15365, true), (15392, false), (15394, true), (30, false)], -- 29442
  [(15366, true), (15394, false), (15396, true), (30, false)], -- 29443
  [(15367, true), (15396, false), (15398, true), (30, false)], -- 29444
  [(15368, true), (15398, false), (15400, true), (30, false)], -- 29445
  [(15369, true), (15400, false), (15402, true), (30, false)], -- 29446
  [(15370, true), (15402, false), (15404, true), (30, false)], -- 29447
  [(15371, true), (15404, false), (15406, true), (30, false)], -- 29448
  [(15372, true), (15406, false), (15408, true), (30, false)], -- 29449
  [(15373, true), (15408, false), (15410, true), (30, false)], -- 29450
  [(15374, true), (15410, false), (15412, true), (30, false)], -- 29451
  [(15375, true), (15412, false), (15414, true), (30, false)], -- 29452
  [(15376, true), (15414, false), (15416, true), (30, false)], -- 29453
  [(15377, true), (15416, false), (15418, true), (30, false)], -- 29454
  [(15378, true), (15418, false), (15420, true), (30, false)], -- 29455
  [(15379, true), (15420, false), (15422, true), (30, false)], -- 29456
  [(15380, true), (15422, false), (15424, true), (30, false)], -- 29457
  [(15381, true), (15424, false), (15426, true), (30, false)], -- 29458
  [(15382, true), (15426, false), (15428, true), (30, false)], -- 29459
  [(15383, true), (15428, false), (15430, true), (30, false)], -- 29460
  [(15384, true), (15430, false), (15432, true), (30, false)], -- 29461
  [(15385, true), (15432, false), (15434, true), (30, false)], -- 29462
  [(15386, true), (15434, false), (30, false)], -- 29463
  [(15361, false), (15435, true), (30, false)], -- 29464
  [(15435, false), (15436, true), (30, false)], -- 29465
  [(15362, false), (15435, false), (15437, true), (30, false)], -- 29466
  [(15437, false), (15438, true), (30, false)], -- 29467
  [(15363, false), (15437, false), (30, false)], -- 29468
  [(15436, false), (15439, true), (30, false)], -- 29470
  [(15363, false), (15436, false), (15438, true), (30, false)], -- 29471
  [(15438, false), (15440, true), (30, false)], -- 29472
  [(15364, false), (15438, false), (30, false)], -- 29473
  [(15363, false), (15439, true), (30, false)], -- 29474
  [(15364, false), (15439, false), (15440, true), (30, false)], -- 29476
  [(15365, false), (15440, false), (30, false)], -- 29478
  [(15508, false), (588, true)], -- 29658
  [(15508, true), (28, false), (588, false)], -- 29659
  [(15509, false), (1143, true)], -- 29661
  [(15509, true), (29, false), (1143, false)], -- 29662
  [(15510, false), (1696, true)], -- 29664
  [(15510, true), (30, false), (1696, false)], -- 29665
  [(15511, false), (2523, true)], -- 29667
  [(15512, false), (2524, true)], -- 29670
  [(15513, false), (34, true)], -- 29672
  [(15514, false), (35, true)], -- 29675
  [(15515, false), (36, true)], -- 29678
  [(15516, false), (37, true)], -- 29681
  [(15517, false), (38, true)], -- 29684
  [(15518, false), (39, true)], -- 29687
  [(15519, false), (40, true)], -- 29690
  [(15520, false), (41, true)], -- 29693
  [(15521, false), (42, true)], -- 29696
  [(15522, false), (43, true)], -- 29699
  [(15523, false), (44, true)], -- 29702
  [(15524, false), (45, true)], -- 29705
  [(15525, false), (46, true)], -- 29708
  [(15526, false), (47, true)], -- 29711
  [(15527, false), (48, true)], -- 29714
  [(15528, false), (49, true)], -- 29717
  [(15529, false), (50, true)], -- 29720
  [(15530, false), (51, true)], -- 29723
  [(15531, false), (52, true)], -- 29726
  [(15532, false), (53, true)], -- 29729
  [(15533, false), (54, true)], -- 29732
  [(15508, true), (15534, true), (31, false)], -- 29735
  [(15534, false), (15535, true), (31, false)], -- 29736
  [(15509, true), (15534, false), (15536, true), (31, false)], -- 29737
  [(15536, false), (15537, true), (31, false)], -- 29738
  [(15510, true), (15536, false), (15538, true), (31, false)], -- 29739
  [(15538, false), (15539, true), (31, false)], -- 29740
  [(15511, true), (15538, false), (15540, true), (31, false)], -- 29741
  [(15540, false), (15541, true), (31, false)], -- 29742
  [(15509, true), (15535, true), (31, false)], -- 29784
  [(15510, true), (15535, false), (15537, true), (31, false)], -- 29785
  [(15511, true), (15537, false), (15539, true), (31, false)], -- 29786
  [(15512, true), (15539, false), (15541, true), (31, false)], -- 29787
  [(15513, true), (15541, false), (15543, true), (31, false)], -- 29788
  [(15514, true), (15543, false), (15545, true), (31, false)], -- 29789
  [(15515, true), (15545, false), (15547, true), (31, false)], -- 29790
  [(15516, true), (15547, false), (15549, true), (31, false)], -- 29791
  [(15517, true), (15549, false), (15551, true), (31, false)], -- 29792
  [(15518, true), (15551, false), (15553, true), (31, false)], -- 29793
  [(15519, true), (15553, false), (15555, true), (31, false)], -- 29794
  [(15520, true), (15555, false), (15557, true), (31, false)], -- 29795
  [(15521, true), (15557, false), (15559, true), (31, false)], -- 29796
  [(15522, true), (15559, false), (15561, true), (31, false)], -- 29797
  [(15523, true), (15561, false), (15563, true), (31, false)], -- 29798
  [(15524, true), (15563, false), (15565, true), (31, false)], -- 29799
  [(15525, true), (15565, false), (15567, true), (31, false)], -- 29800
  [(15526, true), (15567, false), (15569, true), (31, false)], -- 29801
  [(15527, true), (15569, false), (15571, true), (31, false)], -- 29802
  [(15528, true), (15571, false), (15573, true), (31, false)], -- 29803
  [(15529, true), (15573, false), (15575, true), (31, false)], -- 29804
  [(15530, true), (15575, false), (15577, true), (31, false)], -- 29805
  [(15531, true), (15577, false), (15579, true), (31, false)], -- 29806
  [(15532, true), (15579, false), (15581, true), (31, false)], -- 29807
  [(15533, true), (15581, false), (31, false)], -- 29808
  [(15508, false), (15582, true), (31, false)], -- 29809
  [(15509, false), (15582, false), (15584, true), (31, false)], -- 29811
  [(15510, false), (15584, false), (31, false)], -- 29813
  [(15655, false), (589, true)], -- 30003
  [(15655, true), (28, false), (589, false)], -- 30004
  [(15656, false), (1144, true)], -- 30006
  [(15656, true), (29, false), (1144, false)], -- 30007
  [(15657, false), (1697, true)], -- 30009
  [(15657, true), (30, false), (1697, false)], -- 30010
  [(15658, false), (2248, true)], -- 30012
  [(15659, false), (3072, true)], -- 30015
  [(15660, false), (34, true)], -- 30017
  [(15661, false), (35, true)], -- 30020
  [(15662, false), (36, true)], -- 30023
  [(15663, false), (37, true)], -- 30026
  [(15664, false), (38, true)], -- 30029
  [(15665, false), (39, true)], -- 30032
  [(15666, false), (40, true)], -- 30035
  [(15667, false), (41, true)], -- 30038
  [(15668, false), (42, true)], -- 30041
  [(15669, false), (43, true)], -- 30044
  [(15670, false), (44, true)], -- 30047
  [(15671, false), (45, true)], -- 30050
  [(15672, false), (46, true)], -- 30053
  [(15673, false), (47, true)], -- 30056
  [(15674, false), (48, true)], -- 30059
  [(15675, false), (49, true)], -- 30062
  [(15676, false), (50, true)], -- 30065
  [(15677, false), (51, true)], -- 30068
  [(15678, false), (52, true)], -- 30071
  [(15679, false), (53, true)], -- 30074
  [(15680, false), (54, true)], -- 30077
  [(15655, true), (15681, true), (32, false)], -- 30080
  [(15681, false), (15682, true), (32, false)], -- 30081
  [(15656, true), (15681, false), (15683, true), (32, false)], -- 30082
  [(15683, false), (15684, true), (32, false)], -- 30083
  [(15657, true), (15683, false), (15685, true), (32, false)], -- 30084
  [(15685, false), (15686, true), (32, false)], -- 30085
  [(15658, true), (15685, false), (15687, true), (32, false)], -- 30086
  [(15687, false), (15688, true), (32, false)], -- 30087
  [(15656, true), (15682, true), (32, false)], -- 30129
  [(15657, true), (15682, false), (15684, true), (32, false)], -- 30130
  [(15658, true), (15684, false), (15686, true), (32, false)], -- 30131
  [(15659, true), (15686, false), (15688, true), (32, false)], -- 30132
  [(15660, true), (15688, false), (15690, true), (32, false)], -- 30133
  [(15661, true), (15690, false), (15692, true), (32, false)], -- 30134
  [(15662, true), (15692, false), (15694, true), (32, false)], -- 30135
  [(15663, true), (15694, false), (15696, true), (32, false)], -- 30136
  [(15664, true), (15696, false), (15698, true), (32, false)], -- 30137
  [(15665, true), (15698, false), (15700, true), (32, false)], -- 30138
  [(15666, true), (15700, false), (15702, true), (32, false)], -- 30139
  [(15667, true), (15702, false), (15704, true), (32, false)], -- 30140
  [(15668, true), (15704, false), (15706, true), (32, false)], -- 30141
  [(15669, true), (15706, false), (15708, true), (32, false)], -- 30142
  [(15670, true), (15708, false), (15710, true), (32, false)], -- 30143
  [(15671, true), (15710, false), (15712, true), (32, false)], -- 30144
  [(15672, true), (15712, false), (15714, true), (32, false)], -- 30145
  [(15673, true), (15714, false), (15716, true), (32, false)], -- 30146
  [(15674, true), (15716, false), (15718, true), (32, false)], -- 30147
  [(15675, true), (15718, false), (15720, true), (32, false)], -- 30148
  [(15676, true), (15720, false), (15722, true), (32, false)], -- 30149
  [(15677, true), (15722, false), (15724, true), (32, false)], -- 30150
  [(15678, true), (15724, false), (15726, true), (32, false)], -- 30151
  [(15679, true), (15726, false), (15728, true), (32, false)], -- 30152
  [(15680, true), (15728, false), (32, false)], -- 30153
  [(15655, false), (15729, true), (32, false)], -- 30154
  [(15656, false), (15729, false), (15731, true), (32, false)], -- 30156
  [(15657, false), (15731, false), (32, false)], -- 30158
  [(15802, false), (590, true)], -- 30348
  [(15802, true), (28, false), (590, false)], -- 30349
  [(15803, false), (1145, true)], -- 30351
  [(15803, true), (29, false), (1145, false)], -- 30352
  [(15804, false), (1698, true)], -- 30354
  [(15804, true), (30, false), (1698, false)], -- 30355
  [(15805, false), (2249, true)], -- 30357
  [(15805, true), (31, false), (2249, false)], -- 30358
  [(15806, false), (2798, true)], -- 30360
  [(15807, false), (34, true)], -- 30362
  [(15808, false), (35, true)], -- 30365
  [(15809, false), (36, true)], -- 30368
  [(15810, false), (37, true)], -- 30371
  [(15811, false), (38, true)], -- 30374
  [(15812, false), (39, true)], -- 30377
  [(15813, false), (40, true)], -- 30380
  [(15814, false), (41, true)], -- 30383
  [(15815, false), (42, true)], -- 30386
  [(15816, false), (43, true)], -- 30389
  [(15817, false), (44, true)], -- 30392
  [(15818, false), (45, true)], -- 30395
  [(15819, false), (46, true)], -- 30398
  [(15820, false), (47, true)], -- 30401
  [(15821, false), (48, true)], -- 30404
  [(15822, false), (49, true)], -- 30407
  [(15823, false), (50, true)], -- 30410
  [(15824, false), (51, true)], -- 30413
  [(15825, false), (52, true)], -- 30416
  [(15826, false), (53, true)], -- 30419
  [(15827, false), (54, true)], -- 30422
  [(15802, true), (15828, true), (33, false)], -- 30425
  [(15828, false), (15829, true), (33, false)], -- 30426
  [(15803, true), (15828, false), (15830, true), (33, false)], -- 30427
  [(15830, false), (15831, true), (33, false)], -- 30428
  [(15804, true), (15830, false), (15832, true), (33, false)], -- 30429
  [(15832, false), (15833, true), (33, false)], -- 30430
  [(15805, true), (15832, false), (15834, true), (33, false)], -- 30431
  [(15834, false), (15835, true), (33, false)], -- 30432
  [(15803, true), (15829, true), (33, false)], -- 30474
  [(15804, true), (15829, false), (15831, true), (33, false)], -- 30475
  [(15805, true), (15831, false), (15833, true), (33, false)], -- 30476
  [(15806, true), (15833, false), (15835, true), (33, false)], -- 30477
  [(15807, true), (15835, false), (15837, true), (33, false)], -- 30478
  [(15808, true), (15837, false), (15839, true), (33, false)], -- 30479
  [(15809, true), (15839, false), (15841, true), (33, false)], -- 30480
  [(15810, true), (15841, false), (15843, true), (33, false)], -- 30481
  [(15811, true), (15843, false), (15845, true), (33, false)], -- 30482
  [(15812, true), (15845, false), (15847, true), (33, false)], -- 30483
  [(15813, true), (15847, false), (15849, true), (33, false)], -- 30484
  [(15814, true), (15849, false), (15851, true), (33, false)], -- 30485
  [(15815, true), (15851, false), (15853, true), (33, false)], -- 30486
  [(15816, true), (15853, false), (15855, true), (33, false)], -- 30487
  [(15817, true), (15855, false), (15857, true), (33, false)], -- 30488
  [(15818, true), (15857, false), (15859, true), (33, false)], -- 30489
  [(15819, true), (15859, false), (15861, true), (33, false)], -- 30490
  [(15820, true), (15861, false), (15863, true), (33, false)], -- 30491
  [(15821, true), (15863, false), (15865, true), (33, false)], -- 30492
  [(15822, true), (15865, false), (15867, true), (33, false)], -- 30493
  [(15823, true), (15867, false), (15869, true), (33, false)], -- 30494
  [(15824, true), (15869, false), (15871, true), (33, false)], -- 30495
  [(15825, true), (15871, false), (15873, true), (33, false)], -- 30496
  [(15826, true), (15873, false), (15875, true), (33, false)], -- 30497
  [(15827, true), (15875, false), (33, false)], -- 30498
  [(15802, false), (15876, true), (33, false)], -- 30499
  [(15876, false), (15877, true), (33, false)], -- 30500
  [(15803, false), (15876, false), (15878, true), (33, false)], -- 30501
  [(15804, false), (15878, false), (33, false)], -- 30503
  [(15803, false), (15877, true), (33, false)], -- 30504
  [(15877, false), (15880, true), (33, false)], -- 30505
  [(15804, false), (15877, false), (15879, true), (33, false)], -- 30506
  [(15879, false), (15881, true), (33, false)], -- 30507
  [(15805, false), (15879, false), (33, false)], -- 30508
  [(15804, false), (15880, true), (33, false)], -- 30509
  [(15805, false), (15880, false), (15881, true), (33, false)], -- 30511
  [(15806, false), (15881, false), (33, false)], -- 30513
  [(15949, false), (591, true)], -- 30693
  [(15950, false), (1146, true)], -- 30696
  [(15951, false), (1699, true)], -- 30699
  [(15952, false), (2250, true)], -- 30702
  [(15952, true), (31, false), (2250, false)], -- 30703
  [(15953, false), (2799, true)], -- 30705
  [(15953, true), (32, false), (2799, false)], -- 30706
  [(15954, false), (3346, true)], -- 30708
  [(15954, true), (33, false), (3346, false)], -- 30709
  [(15955, false), (35, true)], -- 30710
  [(15956, false), (36, true)], -- 30713
  [(15957, false), (37, true)], -- 30716
  [(15958, false), (38, true)], -- 30719
  [(15959, false), (39, true)], -- 30722
  [(15960, false), (40, true)], -- 30725
  [(15961, false), (41, true)], -- 30728
  [(15962, false), (42, true)], -- 30731
  [(15963, false), (43, true)], -- 30734
  [(15964, false), (44, true)], -- 30737
  [(15965, false), (45, true)], -- 30740
  [(15966, false), (46, true)], -- 30743
  [(15967, false), (47, true)], -- 30746
  [(15968, false), (48, true)], -- 30749
  [(15969, false), (49, true)], -- 30752
  [(15970, false), (50, true)], -- 30755
  [(15971, false), (51, true)], -- 30758
  [(15972, false), (52, true)], -- 30761
  [(15973, false), (53, true)], -- 30764
  [(15974, false), (54, true)], -- 30767
  [(15949, true), (15950, true), (15951, true), (15952, true), (15953, true), (15954, true), (15955, true), (15956, true), (15957, true), (15958, true), (15959, true), (15960, true), (15961, true), (15962, true), (15963, true), (15964, true), (15965, true), (15966, true), (15967, true), (15968, true), (15969, true), (15970, true), (15971, true), (15972, true), (15973, true), (15974, true), (34, true)], -- 30962
  [(15952, false), (16074, true), (34, true)], -- 30972
  [(16074, false), (16075, true), (34, true)], -- 30973
  [(15953, false), (16075, true), (34, true)], -- 30975
  [(15954, false), (16075, false), (34, true)], -- 30977
  [(16096, false), (592, true)], -- 31038
  [(16097, false), (1147, true)], -- 31041
  [(16098, false), (1700, true)], -- 31044
  [(16099, false), (2251, true)], -- 31047
  [(16099, true), (31, false), (2251, false)], -- 31048
  [(16100, false), (2800, true)], -- 31050
  [(16100, true), (32, false), (2800, false)], -- 31051
  [(16101, false), (3347, true)], -- 31053
  [(16101, true), (33, false), (3347, false)], -- 31054
  [(16102, false), (34, true)], -- 31055
  [(16103, false), (36, true)], -- 31058
  [(16104, false), (37, true)], -- 31061
  [(16105, false), (38, true)], -- 31064
  [(16106, false), (39, true)], -- 31067
  [(16107, false), (40, true)], -- 31070
  [(16108, false), (41, true)], -- 31073
  [(16109, false), (42, true)], -- 31076
  [(16110, false), (43, true)], -- 31079
  [(16111, false), (44, true)], -- 31082
  [(16112, false), (45, true)], -- 31085
  [(16113, false), (46, true)], -- 31088
  [(16114, false), (47, true)], -- 31091
  [(16115, false), (48, true)], -- 31094
  [(16116, false), (49, true)], -- 31097
  [(16117, false), (50, true)], -- 31100
  [(16118, false), (51, true)], -- 31103
  [(16119, false), (52, true)], -- 31106
  [(16120, false), (53, true)], -- 31109
  [(16121, false), (54, true)], -- 31112
  [(16096, true), (16097, true), (16098, true), (16099, true), (16100, true), (16101, true), (16102, true), (16103, true), (16104, true), (16105, true), (16106, true), (16107, true), (16108, true), (16109, true), (16110, true), (16111, true), (16112, true), (16113, true), (16114, true), (16115, true), (16116, true), (16117, true), (16118, true), (16119, true), (16120, true), (16121, true), (35, true)], -- 31307
  [(16099, false), (16221, true), (35, true)], -- 31317
  [(16221, false), (16222, true), (35, true)], -- 31318
  [(16100, false), (16222, true), (35, true)], -- 31320
  [(16101, false), (16222, false), (35, true)], -- 31322
  [(16243, false), (593, true)], -- 31383
  [(16244, false), (1148, true)], -- 31386
  [(16245, false), (1701, true)], -- 31389
  [(16246, false), (2252, true)], -- 31392
  [(16246, true), (31, false), (2252, false)], -- 31393
  [(16247, false), (2801, true)], -- 31395
  [(16247, true), (32, false), (2801, false)], -- 31396
  [(16248, false), (3348, true)], -- 31398
  [(16248, true), (33, false), (3348, false)], -- 31399
  [(16249, false), (34, true)], -- 31400
  [(16250, false), (35, true)], -- 31403
  [(16251, false), (37, true)], -- 31406
  [(16252, false), (38, true)], -- 31409
  [(16253, false), (39, true)], -- 31412
  [(16254, false), (40, true)], -- 31415
  [(16255, false), (41, true)], -- 31418
  [(16256, false), (42, true)], -- 31421
  [(16257, false), (43, true)], -- 31424
  [(16258, false), (44, true)], -- 31427
  [(16259, false), (45, true)], -- 31430
  [(16260, false), (46, true)], -- 31433
  [(16261, false), (47, true)], -- 31436
  [(16262, false), (48, true)], -- 31439
  [(16263, false), (49, true)], -- 31442
  [(16264, false), (50, true)], -- 31445
  [(16265, false), (51, true)], -- 31448
  [(16266, false), (52, true)], -- 31451
  [(16267, false), (53, true)], -- 31454
  [(16268, false), (54, true)], -- 31457
  [(16243, true), (16244, true), (16245, true), (16246, true), (16247, true), (16248, true), (16249, true), (16250, true), (16251, true), (16252, true), (16253, true), (16254, true), (16255, true), (16256, true), (16257, true), (16258, true), (16259, true), (16260, true), (16261, true), (16262, true), (16263, true), (16264, true), (16265, true), (16266, true), (16267, true), (16268, true), (36, true)], -- 31652
  [(16246, false), (16368, true), (36, true)], -- 31662
  [(16368, false), (16369, true), (36, true)], -- 31663
  [(16247, false), (16369, true), (36, true)], -- 31665
  [(16248, false), (16369, false), (36, true)], -- 31667
  [(19036, false), (586, true)], -- 37937
  [(19036, true), (586, false), (308, false)], -- 37939
  [(19037, false), (587, true)], -- 37940
  [(19037, true), (587, false), (309, false)], -- 37942
  [(19038, false), (310, true)], -- 37944
  [(19039, false), (311, true)], -- 37947
  [(19040, false), (312, true)], -- 37950
  [(19041, false), (591, true)], -- 37952
  [(19041, true), (591, false), (313, false)], -- 37954
  [(19042, true), (592, false), (314, false)], -- 37957
  [(19043, false), (593, true)], -- 37958
  [(19043, true), (593, false), (315, false)], -- 37960
  [(19044, false), (316, true)], -- 37962
  [(19045, false), (317, true)], -- 37965
  [(19046, false), (318, true)], -- 37968
  [(19047, false), (319, true)], -- 37971
  [(19048, false), (320, true)], -- 37974
  [(19049, false), (321, true)], -- 37977
  [(19050, false), (322, true)], -- 37980
  [(19051, false), (323, true)], -- 37983
  [(19052, false), (324, true)], -- 37986
  [(19053, false), (325, true)], -- 37989
  [(19054, false), (326, true)], -- 37992
  [(19055, false), (327, true)], -- 37995
  [(19056, false), (328, true)], -- 37998
  [(19057, false), (329, true)], -- 38001
  [(19058, false), (330, true)], -- 38004
  [(19059, false), (331, true)], -- 38007
  [(19060, false), (332, true)], -- 38010
  [(19061, false), (333, true)], -- 38013
  [(19036, true), (19062, true), (307, false)], -- 38015
  [(19062, false), (19063, true), (307, false)], -- 38016
  [(19037, true), (19063, true), (307, false)], -- 38064
  [(19038, true), (19063, false), (19065, true), (307, false)], -- 38065
  [(19039, true), (19065, false), (19067, true), (307, false)], -- 38066
  [(19040, true), (19067, false), (19069, true), (307, false)], -- 38067
  [(19041, true), (19069, false), (19071, true), (307, false)], -- 38068
  [(19042, true), (19071, false), (19073, true), (307, false)], -- 38069
  [(19043, true), (19073, false), (19075, true), (307, false)], -- 38070
  [(19044, true), (19075, false), (19077, true), (307, false)], -- 38071
  [(19045, true), (19077, false), (19079, true), (307, false)], -- 38072
  [(19046, true), (19079, false), (19081, true), (307, false)], -- 38073
  [(19047, true), (19081, false), (19083, true), (307, false)], -- 38074
  [(19048, true), (19083, false), (19085, true), (307, false)], -- 38075
  [(19049, true), (19085, false), (19087, true), (307, false)], -- 38076
  [(19050, true), (19087, false), (19089, true), (307, false)], -- 38077
  [(19051, true), (19089, false), (19091, true), (307, false)], -- 38078
  [(19052, true), (19091, false), (19093, true), (307, false)], -- 38079
  [(19053, true), (19093, false), (19095, true), (307, false)], -- 38080
  [(19054, true), (19095, false), (19097, true), (307, false)], -- 38081
  [(19055, true), (19097, false), (19099, true), (307, false)], -- 38082
  [(19056, true), (19099, false), (19101, true), (307, false)], -- 38083
  [(19057, true), (19101, false), (19103, true), (307, false)], -- 38084
  [(19058, true), (19103, false), (19105, true), (307, false)], -- 38085
  [(19059, true), (19105, false), (19107, true), (307, false)], -- 38086
  [(19060, true), (19107, false), (19109, true), (307, false)], -- 38087
  [(19061, true), (19109, false), (307, false)], -- 38088
  [(19036, false), (19110, true), (307, false)], -- 38089
  [(19037, false), (19110, false), (19112, true), (307, false)], -- 38091
  [(19112, false), (19113, true), (307, false)], -- 38092
  [(19113, false), (19115, true), (307, false)], -- 38097
  [(19115, false), (19117, true), (307, false)], -- 38102
  [(19117, false), (19119, true), (307, false)], -- 38107
  [(19041, false), (19117, false), (307, false)], -- 38108
  [(19119, false), (19121, true), (307, false)], -- 38112
  [(19042, false), (19119, false), (307, false)], -- 38113
  [(19043, false), (19121, false), (307, false)], -- 38118
  [(19354, true), (307, false), (29, false)], -- 38653
  [(19355, true), (587, false), (1419, false)], -- 38656
  [(19356, true), (588, false), (1420, false)], -- 38659
  [(19357, true), (589, false), (1421, false)], -- 38662
  [(19358, true), (590, false), (1422, false)], -- 38665
  [(19354, false), (19476, true), (586, true)], -- 38922
  [(19476, false), (19477, true), (586, true)], -- 38923
  [(19355, false), (19476, false), (586, true)], -- 38924
  [(19477, false), (19478, true), (586, true)], -- 38926
  [(19356, false), (19477, false), (586, true)], -- 38927
  [(19478, false), (19479, true), (586, true)], -- 38929
  [(19357, false), (19478, false), (586, true)], -- 38930
  [(19358, false), (19479, false), (586, true)], -- 38933
  [(19501, true), (307, false), (30, false)], -- 38998
  [(19502, true), (586, false), (1142, false)], -- 39001
  [(19503, true), (588, false), (1972, false)], -- 39004
  [(19504, true), (589, false), (1973, false)], -- 39007
  [(19505, true), (590, false), (1974, false)], -- 39010
  [(19501, false), (19623, true), (587, true)], -- 39267
  [(19623, false), (19624, true), (587, true)], -- 39268
  [(19502, false), (19623, false), (587, true)], -- 39269
  [(19624, false), (19625, true), (587, true)], -- 39271
  [(19503, false), (19624, false), (587, true)], -- 39272
  [(19625, false), (19626, true), (587, true)], -- 39274
  [(19504, false), (19625, false), (587, true)], -- 39275
  [(19505, false), (19626, false), (587, true)], -- 39278
  [(19648, true), (307, false), (31, false)], -- 39343
  [(19649, true), (586, false), (1143, false)], -- 39346
  [(19650, false), (587, true)], -- 39347
  [(19650, false), (1696, true)], -- 39348
  [(19650, true), (587, false), (1696, false)], -- 39349
  [(19651, true), (589, false), (2523, false)], -- 39352
  [(19652, true), (590, false), (2524, false)], -- 39355
  [(19648, false), (19770, true), (588, true)], -- 39612
  [(19770, false), (19771, true), (588, true)], -- 39613
  [(19649, false), (19770, false), (588, true)], -- 39614
  [(19771, false), (19772, true), (588, true)], -- 39616
  [(19650, false), (19771, false), (588, true)], -- 39617
  [(19772, false), (19773, true), (588, true)], -- 39619
  [(19651, false), (19772, false), (588, true)], -- 39620
  [(19652, false), (19773, false), (588, true)], -- 39623
  [(19795, true), (307, false), (32, false)], -- 39688
  [(19796, true), (586, false), (1144, false)], -- 39691
  [(19797, true), (587, false), (1697, false)], -- 39694
  [(19798, true), (588, false), (2248, false)], -- 39697
  [(19799, false), (590, true)], -- 39698
  [(19799, false), (3072, true)], -- 39699
  [(19799, true), (590, false), (3072, false)], -- 39700
  [(19795, false), (19917, true), (589, true)], -- 39957
  [(19917, false), (19918, true), (589, true)], -- 39958
  [(19796, false), (19917, false), (589, true)], -- 39959
  [(19918, false), (19919, true), (589, true)], -- 39961
  [(19797, false), (19918, false), (589, true)], -- 39962
  [(19919, false), (19920, true), (589, true)], -- 39964
  [(19798, false), (19919, false), (589, true)], -- 39965
  [(19799, false), (19920, false), (589, true)], -- 39968
  [(19942, true), (307, false), (33, false)], -- 40033
  [(19943, true), (586, false), (1145, false)], -- 40036
  [(19944, true), (587, false), (1698, false)], -- 40039
  [(19945, true), (588, false), (2249, false)], -- 40042
  [(19942, false), (20064, true), (590, true)], -- 40302
  [(20064, false), (20065, true), (590, true)], -- 40303
  [(19943, false), (20064, false), (590, true)], -- 40304
  [(20065, false), (20066, true), (590, true)], -- 40306
  [(19944, false), (20065, false), (590, true)], -- 40307
  [(19945, false), (20066, false), (590, true)], -- 40310
  [(23176, false), (864, true)], -- 47621
  [(23176, true), (864, false), (307, false)], -- 47623
  [(23177, false), (1142, true)], -- 47624
  [(23177, true), (1142, false), (309, false)], -- 47626
  [(23178, false), (310, true)], -- 47628
  [(23179, false), (311, true)], -- 47631
  [(23180, false), (312, true)], -- 47634
  [(23181, true), (1146, false), (313, false)], -- 47638
  [(23182, true), (1147, false), (314, false)], -- 47641
  [(23183, false), (1148, true)], -- 47642
  [(23183, true), (1148, false), (315, false)], -- 47644
  [(23184, false), (316, true)], -- 47646
  [(23185, false), (317, true)], -- 47649
  [(23186, false), (318, true)], -- 47652
  [(23187, false), (319, true)], -- 47655
  [(23188, false), (320, true)], -- 47658
  [(23189, false), (321, true)], -- 47661
  [(23190, false), (322, true)], -- 47664
  [(23191, false), (323, true)], -- 47667
  [(23192, false), (324, true)], -- 47670
  [(23193, false), (325, true)], -- 47673
  [(23194, false), (326, true)], -- 47676
  [(23195, false), (327, true)], -- 47679
  [(23196, false), (328, true)], -- 47682
  [(23197, false), (329, true)], -- 47685
  [(23198, false), (330, true)], -- 47688
  [(23199, false), (331, true)], -- 47691
  [(23200, false), (332, true)], -- 47694
  [(23201, false), (333, true)], -- 47697
  [(23176, true), (23202, true), (308, false)], -- 47699
  [(23202, false), (23203, true), (308, false)], -- 47700
  [(23177, true), (23203, true), (308, false)], -- 47748
  [(23178, true), (23203, false), (23205, true), (308, false)], -- 47749
  [(23179, true), (23205, false), (23207, true), (308, false)], -- 47750
  [(23180, true), (23207, false), (23209, true), (308, false)], -- 47751
  [(23181, true), (23209, false), (23211, true), (308, false)], -- 47752
  [(23182, true), (23211, false), (23213, true), (308, false)], -- 47753
  [(23183, true), (23213, false), (23215, true), (308, false)], -- 47754
  [(23184, true), (23215, false), (23217, true), (308, false)], -- 47755
  [(23185, true), (23217, false), (23219, true), (308, false)], -- 47756
  [(23186, true), (23219, false), (23221, true), (308, false)], -- 47757
  [(23187, true), (23221, false), (23223, true), (308, false)], -- 47758
  [(23188, true), (23223, false), (23225, true), (308, false)], -- 47759
  [(23189, true), (23225, false), (23227, true), (308, false)], -- 47760
  [(23190, true), (23227, false), (23229, true), (308, false)], -- 47761
  [(23191, true), (23229, false), (23231, true), (308, false)], -- 47762
  [(23192, true), (23231, false), (23233, true), (308, false)], -- 47763
  [(23193, true), (23233, false), (23235, true), (308, false)], -- 47764
  [(23194, true), (23235, false), (23237, true), (308, false)], -- 47765
  [(23195, true), (23237, false), (23239, true), (308, false)], -- 47766
  [(23196, true), (23239, false), (23241, true), (308, false)], -- 47767
  [(23197, true), (23241, false), (23243, true), (308, false)], -- 47768
  [(23198, true), (23243, false), (23245, true), (308, false)], -- 47769
  [(23199, true), (23245, false), (23247, true), (308, false)], -- 47770
  [(23200, true), (23247, false), (23249, true), (308, false)], -- 47771
  [(23201, true), (23249, false), (308, false)], -- 47772
  [(23176, false), (23250, true), (308, false)], -- 47773
  [(23177, false), (23250, false), (23252, true), (308, false)], -- 47775
  [(23252, false), (23253, true), (308, false)], -- 47776
  [(23253, false), (23255, true), (308, false)], -- 47781
  [(23255, false), (23257, true), (308, false)], -- 47786
  [(23257, false), (23259, true), (308, false)], -- 47791
  [(23181, false), (23257, false), (308, false)], -- 47792
  [(23259, false), (23261, true), (308, false)], -- 47796
  [(23182, false), (23259, false), (308, false)], -- 47797
  [(23183, false), (23261, false), (308, false)], -- 47802
  [(23323, true), (308, false), (28, false)], -- 47968
  [(23324, true), (1142, false), (865, false)], -- 47971
  [(23325, true), (1143, false), (866, false)], -- 47974
  [(23326, true), (1144, false), (867, false)], -- 47977
  [(23327, true), (1145, false), (868, false)], -- 47980
  [(23323, false), (23445, true), (864, true)], -- 48237
  [(23445, false), (23446, true), (864, true)], -- 48238
  [(23324, false), (23445, false), (864, true)], -- 48239
  [(23446, false), (23447, true), (864, true)], -- 48241
  [(23325, false), (23446, false), (864, true)], -- 48242
  [(23447, false), (23448, true), (864, true)], -- 48244
  [(23326, false), (23447, false), (864, true)], -- 48245
  [(23327, false), (23448, false), (864, true)], -- 48248
  [(23641, true), (308, false), (30, false)], -- 48682
  [(23642, true), (864, false), (587, false)], -- 48685
  [(23643, true), (1143, false), (1972, false)], -- 48688
  [(23644, true), (1144, false), (1973, false)], -- 48691
  [(23645, true), (1145, false), (1974, false)], -- 48694
  [(23641, false), (23763, true), (1142, true)], -- 48951
  [(23763, false), (23764, true), (1142, true)], -- 48952
  [(23642, false), (23763, false), (1142, true)], -- 48953
  [(23764, false), (23765, true), (1142, true)], -- 48955
  [(23643, false), (23764, false), (1142, true)], -- 48956
  [(23765, false), (23766, true), (1142, true)], -- 48958
  [(23644, false), (23765, false), (1142, true)], -- 48959
  [(23645, false), (23766, false), (1142, true)], -- 48962
  [(23788, true), (308, false), (31, false)], -- 49027
  [(23789, true), (864, false), (588, false)], -- 49030
  [(23790, false), (1142, true)], -- 49031
  [(23790, false), (1696, true)], -- 49032
  [(23790, true), (1142, false), (1696, false)], -- 49033
  [(23791, false), (1144, true)], -- 49034
  [(23791, true), (1144, false), (2523, false)], -- 49036
  [(23792, false), (1145, true)], -- 49037
  [(23792, true), (1145, false), (2524, false)], -- 49039
  [(23788, false), (23910, true), (1143, true)], -- 49296
  [(23910, false), (23911, true), (1143, true)], -- 49297
  [(23789, false), (23910, false), (1143, true)], -- 49298
  [(23911, false), (23912, true), (1143, true)], -- 49300
  [(23790, false), (23911, false), (1143, true)], -- 49301
  [(23912, false), (23913, true), (1143, true)], -- 49303
  [(23791, false), (23912, false), (1143, true)], -- 49304
  [(23792, false), (23913, false), (1143, true)], -- 49307
  [(23935, true), (308, false), (32, false)], -- 49372
  [(23936, true), (864, false), (589, false)], -- 49375
  [(23937, false), (1697, true)], -- 49377
  [(23937, true), (1142, false), (1697, false)], -- 49378
  [(23938, true), (1143, false), (2248, false)], -- 49381
  [(23939, false), (1145, true)], -- 49382
  [(23935, false), (24057, true), (1144, true)], -- 49641
  [(24057, false), (24058, true), (1144, true)], -- 49642
  [(23936, false), (24057, false), (1144, true)], -- 49643
  [(24058, false), (24059, true), (1144, true)], -- 49645
  [(23937, false), (24058, false), (1144, true)], -- 49646
  [(24059, false), (24060, true), (1144, true)], -- 49648
  [(23938, false), (24059, false), (1144, true)], -- 49649
  [(23939, false), (24060, false), (1144, true)], -- 49652
  [(24082, true), (308, false), (33, false)], -- 49717
  [(24083, true), (864, false), (590, false)], -- 49720
  [(24084, false), (1142, true)], -- 49721
  [(24084, true), (1142, false), (1698, false)], -- 49723
  [(24085, true), (1143, false), (2249, false)], -- 49726
  [(24082, false), (24204, true), (1145, true)], -- 49986
  [(24204, false), (24205, true), (1145, true)], -- 49987
  [(24083, false), (24204, false), (1145, true)], -- 49988
  [(24205, false), (24206, true), (1145, true)], -- 49990
  [(24084, false), (24205, false), (1145, true)], -- 49991
  [(24085, false), (24206, false), (1145, true)], -- 49994
  [(27316, false), (865, true)], -- 57305
  [(27316, true), (865, false), (307, false)], -- 57307
  [(27317, false), (1419, true)], -- 57308
  [(27317, true), (1419, false), (308, false)], -- 57310
  [(27318, false), (310, true)], -- 57312
  [(27319, false), (311, true)], -- 57315
  [(27320, false), (312, true)], -- 57318
  [(27321, false), (1699, true)], -- 57320
  [(27321, true), (1699, false), (313, false)], -- 57322
  [(27322, true), (1700, false), (314, false)], -- 57325
  [(27323, false), (1701, true)], -- 57326
  [(27323, true), (1701, false), (315, false)], -- 57328
  [(27324, false), (316, true)], -- 57330
  [(27325, false), (317, true)], -- 57333
  [(27326, false), (318, true)], -- 57336
  [(27327, false), (319, true)], -- 57339
  [(27328, false), (320, true)], -- 57342
  [(27329, false), (321, true)], -- 57345
  [(27330, false), (322, true)], -- 57348
  [(27331, false), (323, true)], -- 57351
  [(27332, false), (324, true)], -- 57354
  [(27333, false), (325, true)], -- 57357
  [(27334, false), (326, true)], -- 57360
  [(27335, false), (327, true)], -- 57363
  [(27336, false), (328, true)], -- 57366
  [(27337, false), (329, true)], -- 57369
  [(27338, false), (330, true)], -- 57372
  [(27339, false), (331, true)], -- 57375
  [(27340, false), (332, true)], -- 57378
  [(27341, false), (333, true)], -- 57381
  [(27316, true), (27342, true), (309, false)], -- 57383
  [(27342, false), (27343, true), (309, false)], -- 57384
  [(27317, true), (27343, true), (309, false)], -- 57432
  [(27318, true), (27343, false), (27345, true), (309, false)], -- 57433
  [(27319, true), (27345, false), (27347, true), (309, false)], -- 57434
  [(27320, true), (27347, false), (27349, true), (309, false)], -- 57435
  [(27321, true), (27349, false), (27351, true), (309, false)], -- 57436
  [(27322, true), (27351, false), (27353, true), (309, false)], -- 57437
  [(27323, true), (27353, false), (27355, true), (309, false)], -- 57438
  [(27324, true), (27355, false), (27357, true), (309, false)], -- 57439
  [(27325, true), (27357, false), (27359, true), (309, false)], -- 57440
  [(27326, true), (27359, false), (27361, true), (309, false)], -- 57441
  [(27327, true), (27361, false), (27363, true), (309, false)], -- 57442
  [(27328, true), (27363, false), (27365, true), (309, false)], -- 57443
  [(27329, true), (27365, false), (27367, true), (309, false)], -- 57444
  [(27330, true), (27367, false), (27369, true), (309, false)], -- 57445
  [(27331, true), (27369, false), (27371, true), (309, false)], -- 57446
  [(27332, true), (27371, false), (27373, true), (309, false)], -- 57447
  [(27333, true), (27373, false), (27375, true), (309, false)], -- 57448
  [(27334, true), (27375, false), (27377, true), (309, false)], -- 57449
  [(27335, true), (27377, false), (27379, true), (309, false)], -- 57450
  [(27336, true), (27379, false), (27381, true), (309, false)], -- 57451
  [(27337, true), (27381, false), (27383, true), (309, false)], -- 57452
  [(27338, true), (27383, false), (27385, true), (309, false)], -- 57453
  [(27339, true), (27385, false), (27387, true), (309, false)], -- 57454
  [(27340, true), (27387, false), (27389, true), (309, false)], -- 57455
  [(27341, true), (27389, false), (309, false)], -- 57456
  [(27316, false), (27390, true), (309, false)], -- 57457
  [(27317, false), (27390, false), (27392, true), (309, false)], -- 57459
  [(27392, false), (27393, true), (309, false)], -- 57460
  [(27393, false), (27395, true), (309, false)], -- 57465
  [(27395, false), (27397, true), (309, false)], -- 57470
  [(27397, false), (27399, true), (309, false)], -- 57475
  [(27321, false), (27397, false), (309, false)], -- 57476
  [(27399, false), (27401, true), (309, false)], -- 57480
  [(27322, false), (27399, false), (309, false)], -- 57481
  [(27323, false), (27401, false), (309, false)], -- 57486
  [(27463, true), (309, false), (28, false)], -- 57652
  [(27464, true), (1419, false), (864, false)], -- 57655
  [(27465, true), (1696, false), (866, false)], -- 57658
  [(27466, true), (1697, false), (867, false)], -- 57661
  [(27467, true), (1698, false), (868, false)], -- 57664
  [(27463, false), (27585, true), (865, true)], -- 57921
  [(27585, false), (27586, true), (865, true)], -- 57922
  [(27464, false), (27585, false), (865, true)], -- 57923
  [(27586, false), (27587, true), (865, true)], -- 57925
  [(27465, false), (27586, false), (865, true)], -- 57926
  [(27587, false), (27588, true), (865, true)], -- 57928
  [(27466, false), (27587, false), (865, true)], -- 57929
  [(27467, false), (27588, false), (865, true)], -- 57932
  [(27610, true), (309, false), (29, false)], -- 57997
  [(27611, false), (865, true)], -- 57998
  [(27611, false), (586, true)], -- 57999
  [(27611, true), (865, false), (586, false)], -- 58000
  [(27612, true), (1696, false), (1420, false)], -- 58003
  [(27613, true), (1697, false), (1421, false)], -- 58006
  [(27614, false), (1698, true)], -- 58007
  [(27614, false), (1422, true)], -- 58008
  [(27614, true), (1698, false), (1422, false)], -- 58009
  [(27610, false), (27732, true), (1419, true)], -- 58266
  [(27732, false), (27733, true), (1419, true)], -- 58267
  [(27611, false), (27732, false), (1419, true)], -- 58268
  [(27733, false), (27734, true), (1419, true)], -- 58270
  [(27612, false), (27733, false), (1419, true)], -- 58271
  [(27734, false), (27735, true), (1419, true)], -- 58273
  [(27613, false), (27734, false), (1419, true)], -- 58274
  [(27614, false), (27735, false), (1419, true)], -- 58277
  [(27928, true), (309, false), (31, false)], -- 58711
  [(27929, true), (865, false), (588, false)], -- 58714
  [(27930, true), (1419, false), (1143, false)], -- 58717
  [(27931, true), (1697, false), (2523, false)], -- 58720
  [(27932, true), (1698, false), (2524, false)], -- 58723
  [(27928, false), (28050, true), (1696, true)], -- 58980
  [(28050, false), (28051, true), (1696, true)], -- 58981
  [(27929, false), (28050, false), (1696, true)], -- 58982
  [(28051, false), (28052, true), (1696, true)], -- 58984
  [(27930, false), (28051, false), (1696, true)], -- 58985
  [(28052, false), (28053, true), (1696, true)], -- 58987
  [(27931, false), (28052, false), (1696, true)], -- 58988
  [(27932, false), (28053, false), (1696, true)], -- 58991
  [(28075, true), (309, false), (32, false)], -- 59056
  [(28076, true), (865, false), (589, false)], -- 59059
  [(28077, true), (1419, false), (1144, false)], -- 59062
  [(28078, true), (1696, false), (2248, false)], -- 59065
  [(28079, true), (1698, false), (3072, false)], -- 59068
  [(28075, false), (28197, true), (1697, true)], -- 59325
  [(28197, false), (28198, true), (1697, true)], -- 59326
  [(28076, false), (28197, false), (1697, true)], -- 59327
  [(28198, false), (28199, true), (1697, true)], -- 59329
  [(28077, false), (28198, false), (1697, true)], -- 59330
  [(28199, false), (28200, true), (1697, true)], -- 59332
  [(28078, false), (28199, false), (1697, true)], -- 59333
  [(28079, false), (28200, false), (1697, true)], -- 59336
  [(28222, true), (309, false), (33, false)], -- 59401
  [(28223, true), (865, false), (590, false)], -- 59404
  [(28224, true), (1419, false), (1145, false)], -- 59407
  [(28225, true), (1696, false), (2249, false)], -- 59410
  [(28226, true), (1697, false), (2798, false)], -- 59413
  [(28222, false), (28344, true), (1698, true)], -- 59670
  [(28344, false), (28345, true), (1698, true)], -- 59671
  [(28223, false), (28344, false), (1698, true)], -- 59672
  [(28345, false), (28346, true), (1698, true)], -- 59674
  [(28224, false), (28345, false), (1698, true)], -- 59675
  [(28346, false), (28347, true), (1698, true)], -- 59677
  [(28225, false), (28346, false), (1698, true)], -- 59678
  [(28226, false), (28347, false), (1698, true)], -- 59681
  [(31456, false), (866, true)], -- 66989
  [(31456, true), (866, false), (307, false)], -- 66991
  [(31457, false), (1420, true)], -- 66992
  [(31457, true), (1420, false), (308, false)], -- 66994
  [(31458, false), (1972, true)], -- 66995
  [(31458, true), (1972, false), (309, false)], -- 66997
  [(31459, false), (311, true)], -- 66999
  [(31460, false), (312, true)], -- 67002
  [(31461, false), (2250, true)], -- 67004
  [(31461, true), (2250, false), (313, false)], -- 67006
  [(31462, false), (2251, true)], -- 67007
  [(31462, true), (2251, false), (314, false)], -- 67009
  [(31463, false), (2252, true)], -- 67010
  [(31463, true), (2252, false), (315, false)], -- 67012
  [(31464, false), (316, true)], -- 67014
  [(31465, false), (317, true)], -- 67017
  [(31466, false), (318, true)], -- 67020
  [(31467, false), (319, true)], -- 67023
  [(31468, false), (320, true)], -- 67026
  [(31469, false), (321, true)], -- 67029
  [(31470, false), (322, true)], -- 67032
  [(31471, false), (323, true)], -- 67035
  [(31472, false), (324, true)], -- 67038
  [(31473, false), (325, true)], -- 67041
  [(31474, false), (326, true)], -- 67044
  [(31475, false), (327, true)], -- 67047
  [(31476, false), (328, true)], -- 67050
  [(31477, false), (329, true)], -- 67053
  [(31478, false), (330, true)], -- 67056
  [(31479, false), (331, true)], -- 67059
  [(31480, false), (332, true)], -- 67062
  [(31481, false), (333, true)], -- 67065
  [(31456, true), (31457, true), (31458, true), (31459, true), (31460, true), (31461, true), (31462, true), (31463, true), (31464, true), (31465, true), (31466, true), (31467, true), (31468, true), (31469, true), (31470, true), (31471, true), (31472, true), (31473, true), (31474, true), (31475, true), (31476, true), (31477, true), (31478, true), (31479, true), (31480, true), (31481, true), (310, true)], -- 67259
  [(31456, false), (31578, true), (310, true)], -- 67260
  [(31578, false), (31579, true), (310, true)], -- 67261
  [(31457, false), (31578, false), (310, true)], -- 67262
  [(31457, false), (31579, true), (310, true)], -- 67263
  [(31579, false), (31580, true), (310, true)], -- 67264
  [(31458, false), (31579, false), (310, true)], -- 67265
  [(31580, false), (31581, true), (310, true)], -- 67267
  [(31581, false), (31582, true), (310, true)], -- 67270
  [(31582, false), (31583, true), (310, true)], -- 67273
  [(31461, false), (31582, false), (310, true)], -- 67274
  [(31461, false), (31583, true), (310, true)], -- 67275
  [(31583, false), (31584, true), (310, true)], -- 67276
  [(31462, false), (31583, false), (310, true)], -- 67277
  [(31462, false), (31584, true), (310, true)], -- 67278
  [(31463, false), (31584, false), (310, true)], -- 67280
  [(31606, true), (2248, false), (867, false)], -- 67345
  [(31607, true), (2249, false), (868, false)], -- 67348
  [(31606, false), (31728, true), (866, true)], -- 67614
  [(31607, false), (31728, false), (866, true)], -- 67616
  [(31751, true), (866, false), (586, false)], -- 67684
  [(31752, true), (1972, false), (1419, false)], -- 67687
  [(31753, true), (2248, false), (1421, false)], -- 67690
  [(31754, true), (2249, false), (1422, false)], -- 67693
  [(31751, false), (31873, true), (1420, true)], -- 67953
  [(31873, false), (31874, true), (1420, true)], -- 67954
  [(31752, false), (31874, true), (1420, true)], -- 67956
  [(31874, false), (31875, true), (1420, true)], -- 67957
  [(31753, false), (31874, false), (1420, true)], -- 67958
  [(31753, false), (31875, true), (1420, true)], -- 67959
  [(31754, false), (31875, false), (1420, true)], -- 67961
  [(31897, false), (310, true)], -- 68024
  [(31898, false), (866, true)], -- 68027
  [(31898, false), (587, true)], -- 68028
  [(31898, true), (866, false), (587, false)], -- 68029
  [(31899, false), (1420, true)], -- 68030
  [(31899, true), (1420, false), (1142, false)], -- 68032
  [(31900, false), (1973, true)], -- 68034
  [(31900, true), (2248, false), (1973, false)], -- 68035
  [(31901, false), (2249, true)], -- 68036
  [(31901, true), (2249, false), (1974, false)], -- 68038
  [(31897, true), (31898, true), (31899, true), (31900, true), (31901, true), (31902, true), (31903, true), (31904, true), (31905, true), (31906, true), (31907, true), (31908, true), (31909, true), (31910, true), (31911, true), (31912, true), (31913, true), (31914, true), (31915, true), (31916, true), (31917, true), (31918, true), (31919, true), (31920, true), (31921, true), (31922, true), (1972, true)], -- 68294
  [(31898, false), (32020, true), (1972, true)], -- 68298
  [(32020, false), (32021, true), (1972, true)], -- 68299
  [(31899, false), (32021, true), (1972, true)], -- 68301
  [(32021, false), (32022, true), (1972, true)], -- 68302
  [(31900, false), (32021, false), (1972, true)], -- 68303
  [(31900, false), (32022, true), (1972, true)], -- 68304
  [(32022, false), (32023, true), (1972, true)], -- 68305
  [(31901, false), (32022, false), (1972, true)], -- 68306
  [(32023, false), (32024, true), (1972, true)], -- 68308
  [(31902, false), (32023, false), (1972, true)], -- 68309
  [(32024, false), (32025, true), (1972, true)], -- 68311
  [(31903, false), (32024, false), (1972, true)], -- 68312
  [(32025, false), (32026, true), (1972, true)], -- 68314
  [(31904, false), (32025, false), (1972, true)], -- 68315
  [(32026, false), (32027, true), (1972, true)], -- 68317
  [(31905, false), (32026, false), (1972, true)], -- 68318
  [(32027, false), (32028, true), (1972, true)], -- 68320
  [(31906, false), (32027, false), (1972, true)], -- 68321
  [(32028, false), (32029, true), (1972, true)], -- 68323
  [(31907, false), (32028, false), (1972, true)], -- 68324
  [(32029, false), (32030, true), (1972, true)], -- 68326
  [(31908, false), (32029, false), (1972, true)], -- 68327
  [(32030, false), (32031, true), (1972, true)], -- 68329
  [(31909, false), (32030, false), (1972, true)], -- 68330
  [(32031, false), (32032, true), (1972, true)], -- 68332
  [(31910, false), (32031, false), (1972, true)], -- 68333
  [(32032, false), (32033, true), (1972, true)], -- 68335
  [(31911, false), (32032, false), (1972, true)], -- 68336
  [(32033, false), (32034, true), (1972, true)], -- 68338
  [(31912, false), (32033, false), (1972, true)], -- 68339
  [(32034, false), (32035, true), (1972, true)], -- 68341
  [(31913, false), (32034, false), (1972, true)], -- 68342
  [(32035, false), (32036, true), (1972, true)], -- 68344
  [(31914, false), (32035, false), (1972, true)], -- 68345
  [(32036, false), (32037, true), (1972, true)], -- 68347
  [(31915, false), (32036, false), (1972, true)], -- 68348
  [(32037, false), (32038, true), (1972, true)], -- 68350
  [(31916, false), (32037, false), (1972, true)], -- 68351
  [(32038, false), (32039, true), (1972, true)], -- 68353
  [(31917, false), (32038, false), (1972, true)], -- 68354
  [(32039, false), (32040, true), (1972, true)], -- 68356
  [(31918, false), (32039, false), (1972, true)], -- 68357
  [(32040, false), (32041, true), (1972, true)], -- 68359
  [(31919, false), (32040, false), (1972, true)], -- 68360
  [(32041, false), (32042, true), (1972, true)], -- 68362
  [(31920, false), (32041, false), (1972, true)], -- 68363
  [(32042, false), (32043, true), (1972, true)], -- 68365
  [(31921, false), (32042, false), (1972, true)], -- 68366
  [(31922, false), (32043, false), (1972, true)], -- 68368
  [(32513, true), (2248, false), (2799, false)], -- 69442
  [(32514, true), (2249, false), (3346, false)], -- 69445
  [(32515, true), (2251, false), (4164, false)], -- 69448
  [(32513, false), (32635, true), (2250, true)], -- 69711
  [(32635, false), (32636, true), (2250, true)], -- 69712
  [(32514, false), (32636, true), (2250, true)], -- 69714
  [(32515, false), (32636, false), (2250, true)], -- 69716
  [(32807, true), (2248, false), (2801, false)], -- 70132
  [(32808, true), (2249, false), (3348, false)], -- 70135
  [(32810, true), (2251, false), (4436, false)], -- 70141
  [(32807, false), (32929, true), (2252, true)], -- 70401
  [(32929, false), (32930, true), (2252, true)], -- 70402
  [(32808, false), (32930, true), (2252, true)], -- 70404
  [(32930, false), (32931, true), (2252, true)], -- 70405
  [(32810, false), (32931, false), (2252, true)], -- 70409
  [(35596, false), (867, true)], -- 76673
  [(35596, true), (867, false), (307, false)], -- 76675
  [(35597, false), (1421, true)], -- 76676
  [(35597, true), (1421, false), (308, false)], -- 76678
  [(35598, false), (1973, true)], -- 76679
  [(35598, true), (1973, false), (309, false)], -- 76681
  [(35599, false), (310, true)], -- 76683
  [(35600, false), (312, true)], -- 76686
  [(35601, false), (2799, true)], -- 76688
  [(35601, true), (2799, false), (313, false)], -- 76690
  [(35602, false), (2800, true)], -- 76691
  [(35602, true), (2800, false), (314, false)], -- 76693
  [(35603, false), (2801, true)], -- 76694
  [(35604, false), (316, true)], -- 76698
  [(35605, false), (317, true)], -- 76701
  [(35606, false), (318, true)], -- 76704
  [(35607, false), (319, true)], -- 76707
  [(35608, false), (320, true)], -- 76710
  [(35609, false), (321, true)], -- 76713
  [(35610, false), (322, true)], -- 76716
  [(35611, false), (323, true)], -- 76719
  [(35612, false), (324, true)], -- 76722
  [(35613, false), (325, true)], -- 76725
  [(35614, false), (326, true)], -- 76728
  [(35615, false), (327, true)], -- 76731
  [(35616, false), (328, true)], -- 76734
  [(35617, false), (329, true)], -- 76737
  [(35618, false), (330, true)], -- 76740
  [(35619, false), (331, true)], -- 76743
  [(35620, false), (332, true)], -- 76746
  [(35621, false), (333, true)], -- 76749
  [(35596, true), (35597, true), (35598, true), (35599, true), (35600, true), (35601, true), (35602, true), (35603, true), (35604, true), (35605, true), (35606, true), (35607, true), (35608, true), (35609, true), (35610, true), (35611, true), (35612, true), (35613, true), (35614, true), (35615, true), (35616, true), (35617, true), (35618, true), (35619, true), (35620, true), (35621, true), (311, true)], -- 76943
  [(35596, false), (35718, true), (311, true)], -- 76944
  [(35718, false), (35719, true), (311, true)], -- 76945
  [(35597, false), (35718, false), (311, true)], -- 76946
  [(35597, false), (35719, true), (311, true)], -- 76947
  [(35598, false), (35719, false), (311, true)], -- 76949
  [(35601, false), (35723, true), (311, true)], -- 76959
  [(35602, false), (35723, false), (311, true)], -- 76961
  [(35744, true), (1421, false), (864, false)], -- 77023
  [(35745, true), (1973, false), (865, false)], -- 77026
  [(35746, true), (2523, false), (866, false)], -- 77029
  [(35747, true), (2798, false), (868, false)], -- 77032
  [(35744, false), (35866, true), (867, true)], -- 77292
  [(35866, false), (35867, true), (867, true)], -- 77293
  [(35745, false), (35867, true), (867, true)], -- 77295
  [(35867, false), (35868, true), (867, true)], -- 77296
  [(35746, false), (35867, false), (867, true)], -- 77297
  [(35746, false), (35868, true), (867, true)], -- 77298
  [(35747, false), (35868, false), (867, true)], -- 77300
  [(35891, true), (867, false), (586, false)], -- 77368
  [(35892, true), (1973, false), (1419, false)], -- 77371
  [(35893, true), (2523, false), (1420, false)], -- 77374
  [(35894, true), (2798, false), (1422, false)], -- 77377
  [(35891, false), (36013, true), (1421, true)], -- 77637
  [(36013, false), (36014, true), (1421, true)], -- 77638
  [(35892, false), (36014, true), (1421, true)], -- 77640
  [(36014, false), (36015, true), (1421, true)], -- 77641
  [(35893, false), (36014, false), (1421, true)], -- 77642
  [(35893, false), (36015, true), (1421, true)], -- 77643
  [(35894, false), (36015, false), (1421, true)], -- 77645
  [(36038, true), (867, false), (587, false)], -- 77713
  [(36039, true), (1421, false), (1142, false)], -- 77716
  [(36040, true), (2523, false), (1972, false)], -- 77719
  [(36041, true), (2798, false), (1974, false)], -- 77722
  [(36038, false), (36160, true), (1973, true)], -- 77982
  [(36160, false), (36161, true), (1973, true)], -- 77983
  [(36039, false), (36161, true), (1973, true)], -- 77985
  [(36161, false), (36162, true), (1973, true)], -- 77986
  [(36040, false), (36161, false), (1973, true)], -- 77987
  [(36040, false), (36162, true), (1973, true)], -- 77988
  [(36041, false), (36162, false), (1973, true)], -- 77990
  [(36653, true), (2523, false), (2250, false)], -- 79126
  [(36654, true), (2798, false), (3346, false)], -- 79129
  [(36655, true), (2800, false), (4164, false)], -- 79132
  [(36653, false), (36775, true), (2799, true)], -- 79395
  [(36775, false), (36776, true), (2799, true)], -- 79396
  [(36654, false), (36776, true), (2799, true)], -- 79398
  [(36655, false), (36776, false), (2799, true)], -- 79400
  [(36947, true), (2523, false), (2252, false)], -- 79816
  [(36948, true), (2798, false), (3348, false)], -- 79819
  [(36950, true), (2800, false), (4436, false)], -- 79825
  [(36947, false), (37069, true), (2801, true)], -- 80085
  [(37069, false), (37070, true), (2801, true)], -- 80086
  [(36948, false), (37070, true), (2801, true)], -- 80088
  [(37070, false), (37071, true), (2801, true)], -- 80089
  [(36950, false), (37071, false), (2801, true)], -- 80093
  [(39736, false), (868, true)], -- 86357
  [(39736, true), (868, false), (307, false)], -- 86359
  [(39737, false), (1422, true)], -- 86360
  [(39737, true), (1422, false), (308, false)], -- 86362
  [(39738, false), (1974, true)], -- 86363
  [(39738, true), (1974, false), (309, false)], -- 86365
  [(39739, false), (310, true)], -- 86367
  [(39740, false), (311, true)], -- 86370
  [(39741, false), (3346, true)], -- 86372
  [(39741, true), (3346, false), (313, false)], -- 86374
  [(39742, false), (3347, true)], -- 86375
  [(39742, true), (3347, false), (314, false)], -- 86377
  [(39743, false), (3348, true)], -- 86378
  [(39743, true), (3348, false), (315, false)], -- 86380
  [(39744, false), (316, true)], -- 86382
  [(39745, false), (317, true)], -- 86385
  [(39746, false), (318, true)], -- 86388
  [(39747, false), (319, true)], -- 86391
  [(39748, false), (320, true)], -- 86394
  [(39749, false), (321, true)], -- 86397
  [(39750, false), (322, true)], -- 86400
  [(39751, false), (323, true)], -- 86403
  [(39752, false), (324, true)], -- 86406
  [(39753, false), (325, true)], -- 86409
  [(39754, false), (326, true)], -- 86412
  [(39755, false), (327, true)], -- 86415
  [(39756, false), (328, true)], -- 86418
  [(39757, false), (329, true)], -- 86421
  [(39758, false), (330, true)], -- 86424
  [(39759, false), (331, true)], -- 86427
  [(39760, false), (332, true)], -- 86430
  [(39761, false), (333, true)], -- 86433
  [(39736, true), (39737, true), (39738, true), (39739, true), (39740, true), (39741, true), (39742, true), (39743, true), (39744, true), (39745, true), (39746, true), (39747, true), (39748, true), (39749, true), (39750, true), (39751, true), (39752, true), (39753, true), (39754, true), (39755, true), (39756, true), (39757, true), (39758, true), (39759, true), (39760, true), (39761, true), (312, true)], -- 86627
  [(39736, false), (39858, true), (312, true)], -- 86628
  [(39858, false), (39859, true), (312, true)], -- 86629
  [(39737, false), (39858, false), (312, true)], -- 86630
  [(39737, false), (39859, true), (312, true)], -- 86631
  [(39738, false), (39859, false), (312, true)], -- 86633
  [(39741, false), (39863, true), (312, true)], -- 86643
  [(39863, false), (39864, true), (312, true)], -- 86644
  [(39742, false), (39863, false), (312, true)], -- 86645
  [(39742, false), (39864, true), (312, true)], -- 86646
  [(39743, false), (39864, false), (312, true)], -- 86648
  [(39884, true), (1422, false), (864, false)], -- 86707
  [(39885, true), (1974, false), (865, false)], -- 86710
  [(39886, true), (2524, false), (866, false)], -- 86713
  [(39887, true), (3072, false), (867, false)], -- 86716
  [(39884, false), (40006, true), (868, true)], -- 86976
  [(40006, false), (40007, true), (868, true)], -- 86977
  [(39885, false), (40007, true), (868, true)], -- 86979
  [(40007, false), (40008, true), (868, true)], -- 86980
  [(39886, false), (40007, false), (868, true)], -- 86981
  [(39886, false), (40008, true), (868, true)], -- 86982
  [(39887, false), (40008, false), (868, true)], -- 86984
  [(40031, true), (868, false), (586, false)], -- 87052
  [(40032, true), (1974, false), (1419, false)], -- 87055
  [(40033, true), (2524, false), (1420, false)], -- 87058
  [(40034, true), (3072, false), (1421, false)], -- 87061
  [(40031, false), (40153, true), (1422, true)], -- 87321
  [(40153, false), (40154, true), (1422, true)], -- 87322
  [(40032, false), (40154, true), (1422, true)], -- 87324
  [(40154, false), (40155, true), (1422, true)], -- 87325
  [(40033, false), (40154, false), (1422, true)], -- 87326
  [(40033, false), (40155, true), (1422, true)], -- 87327
  [(40034, false), (40155, false), (1422, true)], -- 87329
  [(40178, true), (868, false), (587, false)], -- 87397
  [(40179, true), (1422, false), (1142, false)], -- 87400
  [(40180, true), (2524, false), (1972, false)], -- 87403
  [(40181, true), (3072, false), (1973, false)], -- 87406
  [(40178, false), (40300, true), (1974, true)], -- 87666
  [(40300, false), (40301, true), (1974, true)], -- 87667
  [(40179, false), (40301, true), (1974, true)], -- 87669
  [(40301, false), (40302, true), (1974, true)], -- 87670
  [(40180, false), (40301, false), (1974, true)], -- 87671
  [(40180, false), (40302, true), (1974, true)], -- 87672
  [(40181, false), (40302, false), (1974, true)], -- 87674
  [(40793, true), (2524, false), (2250, false)], -- 88810
  [(40794, true), (3072, false), (2799, false)], -- 88813
  [(40795, true), (3347, false), (4164, false)], -- 88816
  [(40793, false), (40915, true), (3346, true)], -- 89079
  [(40915, false), (40916, true), (3346, true)], -- 89080
  [(40794, false), (40916, true), (3346, true)], -- 89082
  [(40795, false), (40916, false), (3346, true)], -- 89084
  [(41087, true), (2524, false), (2252, false)], -- 89500
  [(41088, true), (3072, false), (2801, false)], -- 89503
  [(41090, true), (3347, false), (4436, false)], -- 89509
  [(41087, false), (41209, true), (3348, true)], -- 89769
  [(41209, false), (41210, true), (3348, true)], -- 89770
  [(41088, false), (41209, false), (3348, true)], -- 89771
  [(41088, false), (41210, true), (3348, true)], -- 89772
  [(41210, false), (41211, true), (3348, true)], -- 89773
  [(41090, false), (41211, false), (3348, true)], -- 89777
  [(48016, false), (870, true)], -- 105725
  [(48016, true), (870, false), (307, false)], -- 105727
  [(48017, false), (1424, true)], -- 105728
  [(48017, true), (1424, false), (308, false)], -- 105730
  [(48018, false), (1976, true)], -- 105731
  [(48018, true), (1976, false), (309, false)], -- 105733
  [(48019, false), (310, true)], -- 105735
  [(48020, false), (311, true)], -- 105738
  [(48021, false), (312, true)], -- 105741
  [(48022, false), (4164, true)], -- 105743
  [(48023, false), (4436, true)], -- 105746
  [(48023, true), (4436, false), (315, false)], -- 105748
  [(48024, false), (316, true)], -- 105750
  [(48025, false), (317, true)], -- 105753
  [(48026, false), (318, true)], -- 105756
  [(48027, false), (319, true)], -- 105759
  [(48028, false), (320, true)], -- 105762
  [(48029, false), (321, true)], -- 105765
  [(48030, false), (322, true)], -- 105768
  [(48031, false), (323, true)], -- 105771
  [(48032, false), (324, true)], -- 105774
  [(48033, false), (325, true)], -- 105777
  [(48034, false), (326, true)], -- 105780
  [(48035, false), (327, true)], -- 105783
  [(48036, false), (328, true)], -- 105786
  [(48037, false), (329, true)], -- 105789
  [(48038, false), (330, true)], -- 105792
  [(48039, false), (331, true)], -- 105795
  [(48040, false), (332, true)], -- 105798
  [(48041, false), (333, true)], -- 105801
  [(48016, true), (48042, true), (314, false)], -- 105803
  [(48042, false), (48043, true), (314, false)], -- 105804
  [(48017, true), (48042, false), (48044, true), (314, false)], -- 105805
  [(48044, false), (48045, true), (314, false)], -- 105806
  [(48017, true), (48043, true), (314, false)], -- 105852
  [(48018, true), (48043, false), (48045, true), (314, false)], -- 105853
  [(48019, true), (48045, false), (48047, true), (314, false)], -- 105854
  [(48020, true), (48047, false), (48049, true), (314, false)], -- 105855
  [(48021, true), (48049, false), (48051, true), (314, false)], -- 105856
  [(48022, true), (48051, false), (48053, true), (314, false)], -- 105857
  [(48023, true), (48053, false), (48055, true), (314, false)], -- 105858
  [(48024, true), (48055, false), (48057, true), (314, false)], -- 105859
  [(48025, true), (48057, false), (48059, true), (314, false)], -- 105860
  [(48026, true), (48059, false), (48061, true), (314, false)], -- 105861
  [(48027, true), (48061, false), (48063, true), (314, false)], -- 105862
  [(48028, true), (48063, false), (48065, true), (314, false)], -- 105863
  [(48029, true), (48065, false), (48067, true), (314, false)], -- 105864
  [(48030, true), (48067, false), (48069, true), (314, false)], -- 105865
  [(48031, true), (48069, false), (48071, true), (314, false)], -- 105866
  [(48032, true), (48071, false), (48073, true), (314, false)], -- 105867
  [(48033, true), (48073, false), (48075, true), (314, false)], -- 105868
  [(48034, true), (48075, false), (48077, true), (314, false)], -- 105869
  [(48035, true), (48077, false), (48079, true), (314, false)], -- 105870
  [(48036, true), (48079, false), (48081, true), (314, false)], -- 105871
  [(48037, true), (48081, false), (48083, true), (314, false)], -- 105872
  [(48038, true), (48083, false), (48085, true), (314, false)], -- 105873
  [(48039, true), (48085, false), (48087, true), (314, false)], -- 105874
  [(48040, true), (48087, false), (48089, true), (314, false)], -- 105875
  [(48041, true), (48089, false), (314, false)], -- 105876
  [(48016, false), (48090, true), (314, false)], -- 105877
  [(48090, false), (48091, true), (314, false)], -- 105878
  [(48017, false), (48090, false), (48092, true), (314, false)], -- 105879
  [(48092, false), (48093, true), (314, false)], -- 105880
  [(48018, false), (48092, false), (314, false)], -- 105881
  [(48017, false), (48091, true), (314, false)], -- 105882
  [(48018, false), (48091, false), (48093, true), (314, false)], -- 105884
  [(48093, false), (48095, true), (314, false)], -- 105885
  [(48095, false), (48097, true), (314, false)], -- 105890
  [(48097, false), (48099, true), (314, false)], -- 105895
  [(48099, false), (48101, true), (314, false)], -- 105900
  [(48023, false), (48101, false), (314, false)], -- 105906
  [(48163, true), (314, false), (28, false)], -- 106072
  [(48164, true), (1424, false), (864, false)], -- 106075
  [(48165, true), (1976, false), (865, false)], -- 106078
  [(48163, false), (48285, true), (870, true)], -- 106341
  [(48285, false), (48286, true), (870, true)], -- 106342
  [(48164, false), (48285, false), (870, true)], -- 106343
  [(48165, false), (48286, false), (870, true)], -- 106346
  [(48310, true), (314, false), (29, false)], -- 106417
  [(48311, true), (870, false), (586, false)], -- 106420
  [(48312, true), (1976, false), (1419, false)], -- 106423
  [(48310, false), (48432, true), (1424, true)], -- 106686
  [(48432, false), (48433, true), (1424, true)], -- 106687
  [(48311, false), (48432, false), (1424, true)], -- 106688
  [(48312, false), (48433, false), (1424, true)], -- 106691
  [(48457, true), (314, false), (30, false)], -- 106762
  [(48458, true), (870, false), (587, false)], -- 106765
  [(48459, true), (1424, false), (1142, false)], -- 106768
  [(48457, false), (48579, true), (1976, true)], -- 107031
  [(48579, false), (48580, true), (1976, true)], -- 107032
  [(48458, false), (48579, false), (1976, true)], -- 107033
  [(48459, false), (48580, false), (1976, true)], -- 107036
  [(49046, false), (591, true)], -- 108144
  [(49046, true), (870, false), (591, false)], -- 108145
  [(49048, false), (1699, true)], -- 108150
  [(49048, true), (1976, false), (1699, false)], -- 108151
  [(49364, true), (870, false), (593, false)], -- 108859
  [(49365, true), (1424, false), (1148, false)], -- 108862
  [(49366, true), (1976, false), (1701, false)], -- 108865
  [(49364, false), (49486, true), (4436, true)], -- 109128
  [(49486, false), (49487, true), (4436, true)], -- 109129
  [(49365, false), (49486, false), (4436, true)], -- 109130
  [(49365, false), (49487, true), (4436, true)], -- 109131
  [(49366, false), (49487, false), (4436, true)], -- 109133
  [(28, true)], -- 299405
  [(307, true)], -- 299406
  [(29, true)], -- 299407
  [(308, true)], -- 299408
  [(30, true)], -- 299409
  [(309, true)], -- 299410
  [(31, true)], -- 299411
  [(310, false)], -- 299412
  [(32, true)], -- 299413
  [(311, false)], -- 299414
  [(33, true)], -- 299415
  [(312, false)], -- 299416
  [(34, false)], -- 299417
  [(313, true)], -- 299418
  [(35, false)], -- 299419
  [(314, true)], -- 299420
  [(36, false)], -- 299421
  [(315, true)], -- 299422
  [(37, false)], -- 299423
  [(316, false)], -- 299424
  [(38, false)], -- 299425
  [(317, false)], -- 299426
  [(39, false)], -- 299427
  [(318, false)], -- 299428
  [(40, false)], -- 299429
  [(319, false)], -- 299430
  [(41, false)], -- 299431
  [(320, false)], -- 299432
  [(42, false)], -- 299433
  [(321, false)], -- 299434
  [(43, false)], -- 299435
  [(322, false)], -- 299436
  [(44, false)], -- 299437
  [(323, false)], -- 299438
  [(45, false)], -- 299439
  [(324, false)], -- 299440
  [(46, false)], -- 299441
  [(325, false)], -- 299442
  [(47, false)], -- 299443
  [(326, false)], -- 299444
  [(48, false)], -- 299445
  [(327, false)], -- 299446
  [(49, false)], -- 299447
  [(328, false)], -- 299448
  [(50, false)], -- 299449
  [(329, false)], -- 299450
  [(51, false)], -- 299451
  [(330, false)], -- 299452
  [(52, false)], -- 299453
  [(331, false)], -- 299454
  [(53, false)], -- 299455
  [(332, false)], -- 299456
  [(54, false)], -- 299457
  [(333, false)], -- 299458
  [(130816, false), (586, false), (29, false)], -- 299460
  [(130817, false), (587, false), (30, false)], -- 299462
  [(130818, false), (588, false), (31, false)], -- 299464
  [(130819, false), (589, false), (32, false)], -- 299466
  [(130820, false), (590, false), (33, false)], -- 299468
  [(130821, false), (591, true), (34, true)], -- 299469
  [(130822, false), (592, true), (35, true)], -- 299471
  [(130823, false), (593, true), (36, true)], -- 299473
  [(130824, false), (594, true), (37, true)], -- 299475
  [(130825, false), (595, true), (38, true)], -- 299477
  [(130826, false), (596, true), (39, true)], -- 299479
  [(130827, false), (597, true), (40, true)], -- 299481
  [(130828, false), (598, true), (41, true)], -- 299483
  [(130829, false), (599, true), (42, true)], -- 299485
  [(130830, false), (600, true), (43, true)], -- 299487
  [(130831, false), (601, true), (44, true)], -- 299489
  [(130832, false), (602, true), (45, true)], -- 299491
  [(130833, false), (603, true), (46, true)], -- 299493
  [(130834, false), (604, true), (47, true)], -- 299495
  [(130835, false), (605, true), (48, true)], -- 299497
  [(130836, false), (606, true), (49, true)], -- 299499
  [(130837, false), (607, true), (50, true)], -- 299501
  [(130838, false), (608, true), (51, true)], -- 299503
  [(130839, false), (609, true), (52, true)], -- 299505
  [(130840, false), (610, true), (53, true)], -- 299507
  [(130841, false), (611, true), (54, true)], -- 299509
  [(307, false), (28, false), (130816, true), (130817, true), (130818, true), (130819, true), (130820, true), (130821, true), (130822, true), (130823, true), (130824, true), (130825, true), (130826, true), (130827, true), (130828, true), (130829, true), (130830, true), (130831, true), (130832, true), (130833, true), (130834, true), (130835, true), (130836, true), (130837, true), (130838, true), (130839, true), (130840, true), (130841, true)], -- 299511
  [(130842, false), (864, false), (28, false)], -- 299513
  [(130843, false), (1142, false), (30, false)], -- 299515
  [(130844, false), (1143, false), (31, false)], -- 299517
  [(130845, false), (1144, false), (32, false)], -- 299519
  [(130846, false), (1145, false), (33, false)], -- 299521
  [(130847, false), (1146, true), (34, true)], -- 299522
  [(130848, false), (1147, true), (35, true)], -- 299524
  [(130849, false), (1148, true), (36, true)], -- 299526
  [(130850, false), (1149, true), (37, true)], -- 299528
  [(130851, false), (1150, true), (38, true)], -- 299530
  [(130852, false), (1151, true), (39, true)], -- 299532
  [(130853, false), (1152, true), (40, true)], -- 299534
  [(130854, false), (1153, true), (41, true)], -- 299536
  [(130855, false), (1154, true), (42, true)], -- 299538
  [(130856, false), (1155, true), (43, true)], -- 299540
  [(130857, false), (1156, true), (44, true)], -- 299542
  [(130858, false), (1157, true), (45, true)], -- 299544
  [(130859, false), (1158, true), (46, true)], -- 299546
  [(130860, false), (1159, true), (47, true)], -- 299548
  [(130861, false), (1160, true), (48, true)], -- 299550
  [(130862, false), (1161, true), (49, true)], -- 299552
  [(130863, false), (1162, true), (50, true)], -- 299554
  [(130864, false), (1163, true), (51, true)], -- 299556
  [(130865, false), (1164, true), (52, true)], -- 299558
  [(130866, false), (1165, true), (53, true)], -- 299560
  [(130867, false), (1166, true), (54, true)], -- 299562
  [(308, false), (29, false), (130842, true), (130843, true), (130844, true), (130845, true), (130846, true), (130847, true), (130848, true), (130849, true), (130850, true), (130851, true), (130852, true), (130853, true), (130854, true), (130855, true), (130856, true), (130857, true), (130858, true), (130859, true), (130860, true), (130861, true), (130862, true), (130863, true), (130864, true), (130865, true), (130866, true), (130867, true)], -- 299564
  [(130868, false), (865, false), (28, false)], -- 299566
  [(130869, false), (1419, false), (29, false)], -- 299568
  [(130870, false), (1696, false), (31, false)], -- 299570
  [(130871, false), (1697, false), (32, false)], -- 299572
  [(130872, false), (1698, false), (33, false)], -- 299574
  [(130873, false), (1699, true), (34, true)], -- 299575
  [(130874, false), (1700, true), (35, true)], -- 299577
  [(130875, false), (1701, true), (36, true)], -- 299579
  [(130876, false), (1702, true), (37, true)], -- 299581
  [(130877, false), (1703, true), (38, true)], -- 299583
  [(130878, false), (1704, true), (39, true)], -- 299585
  [(130879, false), (1705, true), (40, true)], -- 299587
  [(130880, false), (1706, true), (41, true)], -- 299589
  [(130881, false), (1707, true), (42, true)], -- 299591
  [(130882, false), (1708, true), (43, true)], -- 299593
  [(130883, false), (1709, true), (44, true)], -- 299595
  [(130884, false), (1710, true), (45, true)], -- 299597
  [(130885, false), (1711, true), (46, true)], -- 299599
  [(130886, false), (1712, true), (47, true)], -- 299601
  [(130887, false), (1713, true), (48, true)], -- 299603
  [(130888, false), (1714, true), (49, true)], -- 299605
  [(130889, false), (1715, true), (50, true)], -- 299607
  [(130890, false), (1716, true), (51, true)], -- 299609
  [(130891, false), (1717, true), (52, true)], -- 299611
  [(130892, false), (1718, true), (53, true)], -- 299613
  [(130893, false), (1719, true), (54, true)], -- 299615
  [(309, false), (30, false), (130868, true), (130869, true), (130870, true), (130871, true), (130872, true), (130873, true), (130874, true), (130875, true), (130876, true), (130877, true), (130878, true), (130879, true), (130880, true), (130881, true), (130882, true), (130883, true), (130884, true), (130885, true), (130886, true), (130887, true), (130888, true), (130889, true), (130890, true), (130891, true), (130892, true), (130893, true)] -- 299617
]

def proof : List IntAction := [
  .addRup 1628 #[Int.negSucc 130816, Int.negSucc 586] #[1495, 1547],
  .addRup 1629 #[Int.negSucc 130817, Int.negSucc 587] #[1497, 1548],
  .addRup 1630 #[Int.negSucc 130818, Int.negSucc 588] #[1499, 1549],
  .addRup 1631 #[Int.negSucc 130819, Int.negSucc 589] #[1501, 1550],
  .addRup 1632 #[Int.negSucc 130820, Int.negSucc 590] #[1503, 1551],
  .addRup 1633 #[Int.negSucc 130821, Int.ofNat 592] #[1505, 1552],
  .addRup 1634 #[Int.negSucc 130822, Int.ofNat 593] #[1507, 1553],
  .addRup 1635 #[Int.negSucc 130823, Int.ofNat 594] #[1509, 1554],
  .addRup 1636 #[Int.negSucc 130824, Int.ofNat 595] #[1511, 1555],
  .addRup 1637 #[Int.negSucc 130825, Int.ofNat 596] #[1513, 1556],
  .addRup 1638 #[Int.negSucc 130826, Int.ofNat 597] #[1515, 1557],
  .addRup 1639 #[Int.negSucc 130827, Int.ofNat 598] #[1517, 1558],
  .addRup 1640 #[Int.negSucc 130828, Int.ofNat 599] #[1519, 1559],
  .addRup 1641 #[Int.negSucc 130829, Int.ofNat 600] #[1521, 1560],
  .addRup 1642 #[Int.negSucc 130830, Int.ofNat 601] #[1523, 1561],
  .addRup 1643 #[Int.negSucc 130831, Int.ofNat 602] #[1525, 1562],
  .addRup 1644 #[Int.negSucc 130832, Int.ofNat 603] #[1527, 1563],
  .addRup 1645 #[Int.negSucc 130833, Int.ofNat 604] #[1529, 1564],
  .addRup 1646 #[Int.negSucc 130834, Int.ofNat 605] #[1531, 1565],
  .addRup 1647 #[Int.negSucc 130835, Int.ofNat 606] #[1533, 1566],
  .addRup 1648 #[Int.negSucc 130836, Int.ofNat 607] #[1535, 1567],
  .addRup 1649 #[Int.negSucc 130837, Int.ofNat 608] #[1537, 1568],
  .addRup 1650 #[Int.negSucc 130838, Int.ofNat 609] #[1539, 1569],
  .addRup 1651 #[Int.negSucc 130839, Int.ofNat 610] #[1541, 1570],
  .addRup 1652 #[Int.negSucc 130840, Int.ofNat 611] #[1543, 1571],
  .addRup 1653 #[Int.negSucc 130841, Int.ofNat 612] #[1545, 1572],
  .addRup 1654 #[Int.ofNat 130817, Int.ofNat 130818, Int.ofNat 130819, Int.ofNat 130820, Int.ofNat 130821, Int.ofNat 130822, Int.ofNat 130823, Int.ofNat 130824, Int.ofNat 130825, Int.ofNat 130826, Int.ofNat 130827, Int.ofNat 130828, Int.ofNat 130829, Int.ofNat 130830, Int.ofNat 130831, Int.ofNat 130832, Int.ofNat 130833, Int.ofNat 130834, Int.ofNat 130835, Int.ofNat 130836, Int.ofNat 130837, Int.ofNat 130838, Int.ofNat 130839, Int.ofNat 130840, Int.ofNat 130841, Int.ofNat 130842] #[1493, 1494, 1573],
  .addRup 1655 #[Int.negSucc 130842, Int.negSucc 864] #[1493, 1574],
  .addRup 1656 #[Int.negSucc 130843, Int.negSucc 1142] #[1497, 1575],
  .addRup 1657 #[Int.negSucc 130844, Int.negSucc 1143] #[1499, 1576],
  .addRup 1658 #[Int.negSucc 130845, Int.negSucc 1144] #[1501, 1577],
  .addRup 1659 #[Int.negSucc 130846, Int.negSucc 1145] #[1503, 1578],
  .addRup 1660 #[Int.negSucc 130847, Int.ofNat 1147] #[1505, 1579],
  .addRup 1661 #[Int.negSucc 130848, Int.ofNat 1148] #[1507, 1580],
  .addRup 1662 #[Int.negSucc 130849, Int.ofNat 1149] #[1509, 1581],
  .addRup 1663 #[Int.negSucc 130850, Int.ofNat 1150] #[1511, 1582],
  .addRup 1664 #[Int.negSucc 130851, Int.ofNat 1151] #[1513, 1583],
  .addRup 1665 #[Int.negSucc 130852, Int.ofNat 1152] #[1515, 1584],
  .addRup 1666 #[Int.negSucc 130853, Int.ofNat 1153] #[1517, 1585],
  .addRup 1667 #[Int.negSucc 130854, Int.ofNat 1154] #[1519, 1586],
  .addRup 1668 #[Int.negSucc 130855, Int.ofNat 1155] #[1521, 1587],
  .addRup 1669 #[Int.negSucc 130856, Int.ofNat 1156] #[1523, 1588],
  .addRup 1670 #[Int.negSucc 130857, Int.ofNat 1157] #[1525, 1589],
  .addRup 1671 #[Int.negSucc 130858, Int.ofNat 1158] #[1527, 1590],
  .addRup 1672 #[Int.negSucc 130859, Int.ofNat 1159] #[1529, 1591],
  .addRup 1673 #[Int.negSucc 130860, Int.ofNat 1160] #[1531, 1592],
  .addRup 1674 #[Int.negSucc 130861, Int.ofNat 1161] #[1533, 1593],
  .addRup 1675 #[Int.negSucc 130862, Int.ofNat 1162] #[1535, 1594],
  .addRup 1676 #[Int.negSucc 130863, Int.ofNat 1163] #[1537, 1595],
  .addRup 1677 #[Int.negSucc 130864, Int.ofNat 1164] #[1539, 1596],
  .addRup 1678 #[Int.negSucc 130865, Int.ofNat 1165] #[1541, 1597],
  .addRup 1679 #[Int.negSucc 130866, Int.ofNat 1166] #[1543, 1598],
  .addRup 1680 #[Int.negSucc 130867, Int.ofNat 1167] #[1545, 1599],
  .addRup 1681 #[Int.ofNat 130843, Int.ofNat 130844, Int.ofNat 130845, Int.ofNat 130846, Int.ofNat 130847, Int.ofNat 130848, Int.ofNat 130849, Int.ofNat 130850, Int.ofNat 130851, Int.ofNat 130852, Int.ofNat 130853, Int.ofNat 130854, Int.ofNat 130855, Int.ofNat 130856, Int.ofNat 130857, Int.ofNat 130858, Int.ofNat 130859, Int.ofNat 130860, Int.ofNat 130861, Int.ofNat 130862, Int.ofNat 130863, Int.ofNat 130864, Int.ofNat 130865, Int.ofNat 130866, Int.ofNat 130867, Int.ofNat 130868] #[1495, 1496, 1600],
  .addRup 1682 #[Int.negSucc 130868, Int.negSucc 865] #[1493, 1601],
  .addRup 1683 #[Int.negSucc 130869, Int.negSucc 1419] #[1495, 1602],
  .addRup 1684 #[Int.negSucc 130870, Int.negSucc 1696] #[1499, 1603],
  .addRup 1685 #[Int.negSucc 130871, Int.negSucc 1697] #[1501, 1604],
  .addRup 1686 #[Int.negSucc 130872, Int.negSucc 1698] #[1503, 1605],
  .addRup 1687 #[Int.negSucc 130873, Int.ofNat 1700] #[1505, 1606],
  .addRup 1688 #[Int.negSucc 130874, Int.ofNat 1701] #[1507, 1607],
  .addRup 1689 #[Int.negSucc 130875, Int.ofNat 1702] #[1509, 1608],
  .addRup 1690 #[Int.negSucc 130876, Int.ofNat 1703] #[1511, 1609],
  .addRup 1691 #[Int.negSucc 130877, Int.ofNat 1704] #[1513, 1610],
  .addRup 1692 #[Int.negSucc 130878, Int.ofNat 1705] #[1515, 1611],
  .addRup 1693 #[Int.negSucc 130879, Int.ofNat 1706] #[1517, 1612],
  .addRup 1694 #[Int.negSucc 130880, Int.ofNat 1707] #[1519, 1613],
  .addRup 1695 #[Int.negSucc 130881, Int.ofNat 1708] #[1521, 1614],
  .addRup 1696 #[Int.negSucc 130882, Int.ofNat 1709] #[1523, 1615],
  .addRup 1697 #[Int.negSucc 130883, Int.ofNat 1710] #[1525, 1616],
  .addRup 1698 #[Int.negSucc 130884, Int.ofNat 1711] #[1527, 1617],
  .addRup 1699 #[Int.negSucc 130885, Int.ofNat 1712] #[1529, 1618],
  .addRup 1700 #[Int.negSucc 130886, Int.ofNat 1713] #[1531, 1619],
  .addRup 1701 #[Int.negSucc 130887, Int.ofNat 1714] #[1533, 1620],
  .addRup 1702 #[Int.negSucc 130888, Int.ofNat 1715] #[1535, 1621],
  .addRup 1703 #[Int.negSucc 130889, Int.ofNat 1716] #[1537, 1622],
  .addRup 1704 #[Int.negSucc 130890, Int.ofNat 1717] #[1539, 1623],
  .addRup 1705 #[Int.negSucc 130891, Int.ofNat 1718] #[1541, 1624],
  .addRup 1706 #[Int.negSucc 130892, Int.ofNat 1719] #[1543, 1625],
  .addRup 1707 #[Int.negSucc 130893, Int.ofNat 1720] #[1545, 1626],
  .addRup 1708 #[Int.ofNat 130869, Int.ofNat 130870, Int.ofNat 130871, Int.ofNat 130872, Int.ofNat 130873, Int.ofNat 130874, Int.ofNat 130875, Int.ofNat 130876, Int.ofNat 130877, Int.ofNat 130878, Int.ofNat 130879, Int.ofNat 130880, Int.ofNat 130881, Int.ofNat 130882, Int.ofNat 130883, Int.ofNat 130884, Int.ofNat 130885, Int.ofNat 130886, Int.ofNat 130887, Int.ofNat 130888, Int.ofNat 130889, Int.ofNat 130890, Int.ofNat 130891, Int.ofNat 130892, Int.ofNat 130893, Int.ofNat 130894] #[1497, 1498, 1627],
  .addRup 1709 #[Int.ofNat 1425, Int.ofNat 19043, Int.ofNat 27323, Int.ofNat 48046, Int.ofNat 49047, Int.ofNat 49049] #[1494, 1495, 1498, 1500, 1502, 1504, 1508, 1510, 1512, 1514, 1516, 1518, 1520, 1522, 1524, 1526, 1528, 1530, 1532, 1534, 1536, 1538, 1540, 1542, 1544, 1546, 673, 940, 674, 941, 675, 942, 1467, 681, 948, 682, 949, 683, 950, 684, 951, 685, 952, 686, 953, 687, 954, 688, 955, 689, 956, 690, 957, 691, 958, 692, 959, 693, 960, 694, 961, 695, 962, 696, 963, 697, 964, 698, 965, 725, 992, 724, 991, 723, 990, 722, 989, 721, 988, 720, 987, 719, 986, 718, 985, 717, 984, 716, 983, 715, 982, 714, 981, 713, 980, 712, 979, 711, 978, 710, 977, 709, 976, 708, 975, 1391, 1470, 1422, 1423, 1424, 1393, 1484, 943, 1421, 1419, 1389, 1448, 1482, 676, 1471, 1472, 1449, 1454, 1455, 1456, 1457, 1458, 1459, 1400, 1473, 1468, 1469, 669, 938, 699, 968, 969, 970, 971, 972, 973, 974, 946, 1487, 1492, 700, 702, 703, 704, 705, 706, 707, 679, 1485, 1488, 1489],
  .addRup 1710 #[Int.ofNat 588, Int.negSucc 19502] #[1494, 1497, 749, 754, 756],
  .addRup 1711 #[Int.ofNat 1977, Int.negSucc 1424, Int.ofNat 19043, Int.ofNat 23182, Int.ofNat 23183, Int.ofNat 48046, Int.ofNat 49047] #[1494, 1496, 1497, 1500, 1502, 1504, 1508, 1510, 1512, 1514, 1516, 1518, 1520, 1522, 1524, 1526, 1528, 1530, 1532, 1534, 1536, 1538, 1540, 1542, 1544, 1546, 673, 806, 674, 807, 675, 808, 1474, 681, 813, 682, 814, 683, 815, 684, 816, 685, 817, 686, 818, 687, 819, 688, 820, 689, 821, 690, 822, 691, 823, 692, 824, 693, 825, 694, 826, 695, 827, 696, 828, 697, 829, 698, 830, 725, 857, 724, 856, 723, 855, 722, 854, 721, 853, 720, 852, 719, 851, 718, 850, 717, 849, 716, 848, 715, 847, 714, 846, 713, 845, 712, 844, 711, 843, 710, 842, 709, 841, 708, 840, 1392, 1393, 1477, 1424, 1478, 1479, 1420, 1480, 1419, 1448, 1450, 1476, 1389, 1451, 1455, 1456, 1457, 1458, 1459, 1400, 804, 1482, 1475, 833, 834, 835, 836, 837, 838, 839, 811, 1486, 676, 671, 1490, 701, 1488, 702, 1485, 703, 679, 704, 707, 705, 706],
  .addRup 1712 #[Int.ofNat 23183, Int.ofNat 19043, Int.ofNat 23182, Int.ofNat 27323, Int.ofNat 48046, Int.ofNat 49047, Int.ofNat 49049] #[1493, 1494, 1496, 1498, 1500, 1502, 1504, 1508, 1510, 1512, 1514, 1516, 1518, 1520, 1522, 1524, 1526, 1528, 1530, 1532, 1534, 1536, 1538, 1540, 1542, 1544, 1546, 806, 940, 807, 941, 808, 942, 1460, 813, 948, 814, 949, 815, 950, 816, 951, 817, 952, 818, 953, 819, 954, 820, 955, 821, 956, 822, 957, 823, 958, 824, 959, 825, 960, 826, 961, 827, 962, 828, 963, 829, 964, 830, 965, 857, 992, 856, 991, 855, 990, 854, 989, 853, 988, 852, 987, 851, 986, 850, 985, 849, 984, 848, 983, 847, 982, 846, 981, 845, 980, 844, 979, 843, 978, 842, 977, 841, 976, 840, 975, 1709, 1711, 1392, 1484, 1394, 1453, 943, 1452, 1454, 1450, 1455, 1448, 1456, 1390, 1457, 1463, 1458, 1464, 1465, 1459, 1466, 1461, 1400, 1462, 802, 936, 831, 966, 832, 967, 834, 969, 835, 970, 836, 971, 837, 972, 838, 973, 839, 974, 811, 946, 1486, 1487, 1491, 1492],
  .addRup 1713 #[Int.negSucc 23937, Int.ofNat 1145] #[1496, 1501, 911, 917, 918, 921],
  .addRup 1714 #[Int.negSucc 23790, Int.ofNat 1144] #[1496, 1499, 894, 903, 904, 907],
  .addRup 1715 #[Int.negSucc 1696, Int.negSucc 1143, Int.ofNat 23791, Int.ofNat 130885, Int.ofNat 130887, Int.ofNat 130891] #[1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503, 1504, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 881, 749, 89, 762, 911, 925, 146, 221, 296, 435, 501, 147, 222, 297, 436, 502, 148, 223, 298, 437, 503, 149, 224, 299, 438, 504, 150, 225, 300, 439, 505, 151, 226, 301, 440, 506, 152, 227, 302, 441, 507, 153, 228, 303, 442, 508, 154, 229, 304, 443, 509, 155, 230, 305, 444, 510, 156, 231, 306, 445, 511, 157, 232, 307, 446, 512, 158, 233, 308, 447, 513, 159, 234, 309, 448, 514, 160, 235, 310, 449, 515, 161, 236, 311, 450, 516, 162, 237, 312, 451, 517, 163, 238, 313, 452, 518, 164, 239, 314, 453, 519, 165, 240, 315, 454, 520, 166, 241, 316, 455, 521, 199, 274, 349, 488, 554, 198, 273, 348, 487, 553, 197, 272, 347, 486, 552, 196, 271, 346, 485, 551, 195, 270, 345, 484, 550, 194, 269, 344, 483, 549, 193, 268, 343, 482, 548, 192, 267, 342, 481, 547, 191, 266, 341, 480, 546, 190, 265, 340, 479, 545, 189, 264, 339, 478, 544, 188, 263, 338, 477, 543, 187, 262, 337, 476, 542, 186, 261, 336, 475, 541, 185, 260, 335, 474, 540, 184, 259, 334, 473, 539, 183, 258, 333, 472, 538, 182, 257, 332, 471, 537, 181, 256, 331, 470, 536, 180, 255, 330, 469, 535, 179, 254, 329, 468, 534, 324, 463, 529, 365, 367, 1684, 898, 426, 288, 886, 425, 887, 424, 889, 890, 363, 891, 892, 883, 769, 893, 290, 770, 771, 773, 763, 766, 211, 286, 754, 242, 317, 755, 243, 319, 757, 321, 759, 760, 322, 323, 761, 328, 292, 294, 1215, 884, 752, 1302, 885, 753, 1246, 429, 917, 427, 1334, 494, 930, 492, 1243, 1245, 918, 456, 1331, 1333, 931, 522, 1242, 1213, 920, 458, 1330, 1300, 933, 524, 1211, 217, 923, 1298, 219, 935, 142, 915, 144, 253, 929, 433, 178, 252, 498, 462, 177, 245, 251, 528, 460, 244, 215, 526, 431, 213, 1075, 496, 1685, 1683, 1107, 1686, 1105, 1073, 140, 176, 175, 138, 90, 1682, 91, 92, 93, 94, 95, 96, 97, 98, 1687, 99, 100, 1688, 101, 102, 1689, 103, 104, 1690, 105, 106, 1691, 107, 108, 1692, 109, 110, 1693, 111, 112, 1694, 113, 114, 1695, 115, 116, 1696, 117, 1697, 119, 120, 121, 1699, 123, 124, 125, 126, 1701, 127, 128, 1702, 129, 1703, 131, 132, 133, 134, 1705, 135, 1706, 1707, 1708],
  .addRup 1716 #[Int.negSucc 15391, Int.negSucc 15243] #[1495, 1496, 1497, 1498, 1502, 1504, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 221, 296, 222, 297, 223, 298, 224, 299, 225, 300, 226, 301, 227, 302, 228, 303, 229, 304, 230, 305, 231, 306, 232, 307, 233, 308, 234, 309, 235, 310, 236, 311, 237, 312, 238, 313, 239, 314, 240, 315, 241, 316, 274, 349, 273, 348, 272, 347, 271, 346, 270, 345, 269, 344, 268, 343, 267, 342, 266, 341, 265, 340, 264, 339, 263, 338, 262, 337, 261, 336, 260, 335, 259, 334, 258, 333, 257, 332, 256, 331, 255, 330, 254, 329, 324, 322, 323, 328, 292, 294, 1215, 1302, 1246, 1334, 1245, 1333, 1213, 1300, 217, 219, 252, 253],
  .addRup 1717 #[Int.negSucc 1421, Int.negSucc 1422, Int.negSucc 15387, Int.negSucc 15537] #[1496, 1497, 1498, 1499, 1502, 1504, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 296, 370, 297, 371, 298, 372, 299, 373, 300, 374, 301, 375, 302, 376, 303, 377, 304, 378, 305, 379, 306, 380, 307, 381, 308, 382, 309, 383, 310, 384, 311, 385, 312, 386, 313, 387, 314, 388, 315, 389, 316, 390, 349, 423, 348, 422, 347, 421, 346, 420, 345, 419, 344, 418, 343, 417, 342, 416, 341, 415, 340, 414, 339, 413, 338, 412, 337, 411, 336, 410, 335, 409, 334, 408, 333, 407, 332, 406, 331, 405, 330, 404, 329, 403, 318, 1300, 1213, 1333, 1245, 1334, 1246, 1302, 1215, 294, 292, 328, 327, 320, 326, 319, 290, 288, 1363, 1272, 1368, 1277, 1370, 1279, 1364, 1273, 369, 368, 402, 401],
  .addRup 1718 #[Int.negSucc 1974, Int.negSucc 587, Int.negSucc 1143, Int.ofNat 15216, Int.ofNat 27612] #[1493, 1494, 1495, 1496, 1497, 1498, 1502, 1503, 1504, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 868, 881, 146, 221, 147, 222, 148, 223, 149, 224, 150, 225, 151, 226, 152, 227, 153, 228, 154, 229, 155, 230, 156, 231, 157, 232, 158, 233, 159, 234, 160, 235, 161, 236, 162, 237, 163, 238, 164, 239, 165, 240, 166, 241, 199, 274, 198, 273, 197, 272, 196, 271, 195, 270, 194, 269, 193, 268, 192, 267, 191, 266, 190, 265, 189, 264, 188, 263, 187, 262, 186, 261, 185, 260, 184, 259, 183, 258, 182, 257, 181, 256, 180, 255, 179, 254, 1302, 295, 287, 1334, 361, 350, 1331, 1333, 357, 1330, 1300, 353, 1298, 219, 352, 144, 253, 289, 178, 886, 172, 888, 882, 136, 873, 167, 874, 168, 877, 870, 140, 176, 171, 177, 169, 142, 138, 1211, 1019, 1242, 211, 1244, 242, 1213, 244, 217, 245, 252],
  .addRup 1719 #[Int.ofNat 1145, Int.negSucc 1143, Int.ofNat 15658, Int.negSucc 15681] #[1496, 1501, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 911, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 488, 487, 486, 485, 484, 483, 482, 481, 480, 479, 478, 477, 476, 475, 474, 473, 472, 471, 470, 469, 468, 463, 429, 917, 458, 918, 460, 920, 462, 923, 433, 915],
  .addRup 1720 #[Int.ofNat 1146, Int.negSucc 1143, Int.ofNat 15805, Int.negSucc 15828] #[1496, 1503, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 925, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 554, 553, 552, 551, 550, 549, 548, 547, 546, 545, 544, 543, 542, 541, 540, 539, 538, 537, 536, 535, 534, 529, 494, 930, 524, 931, 526, 528, 498, 933, 929, 935],
  .addRup 1721 #[Int.negSucc 1145, Int.negSucc 1301, Int.ofNat 130843, Int.ofNat 130844, Int.ofNat 130845, Int.ofNat 130846, Int.ofNat 130848, Int.ofNat 130849, Int.ofNat 130850, Int.ofNat 130859, Int.ofNat 130861, Int.ofNat 130865] #[50, 51, 52, 53, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 1659, 55, 57, 59, 61, 63, 65, 67, 69, 73, 77, 79, 81, 82, 1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1672, 1674, 1675, 1676, 84, 85, 86, 87, 1678, 88, 1679, 1680, 1681],
  .addRup 1722 #[Int.negSucc 1144, Int.negSucc 1145, Int.negSucc 1299, Int.ofNat 130843, Int.ofNat 130844, Int.ofNat 130845, Int.ofNat 130848, Int.ofNat 130849, Int.ofNat 130850, Int.ofNat 130859, Int.ofNat 130861, Int.ofNat 130865] #[1658, 49, 1721],
  .addRup 1723 #[Int.ofNat 1145, Int.negSucc 864, Int.negSucc 1143, Int.ofNat 15658] #[1496, 1501, 911, 917, 1719, 456, 427, 919, 912],
  .addRup 1724 #[Int.negSucc 1698, Int.negSucc 1143, Int.negSucc 15243, Int.ofNat 15393, Int.ofNat 24085, Int.ofNat 27615] #[1495, 1496, 1497, 1498, 1502, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 881, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 274, 273, 272, 271, 270, 269, 268, 267, 266, 265, 264, 263, 262, 261, 260, 259, 258, 257, 256, 255, 254, 1024, 928, 219, 288, 886, 253, 325, 887, 252, 890, 217, 883, 1213, 290, 1245, 326, 1246, 327, 1215, 292],
  .addRup 1725 #[Int.negSucc 15097, Int.negSucc 15243] #[1493, 1494, 1495, 1496, 1502, 1504, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 146, 221, 147, 222, 148, 223, 149, 224, 150, 225, 151, 226, 152, 227, 153, 228, 154, 229, 155, 230, 156, 231, 157, 232, 158, 233, 159, 234, 160, 235, 161, 236, 162, 237, 163, 238, 164, 239, 165, 240, 166, 241, 199, 274, 198, 273, 197, 272, 196, 271, 195, 270, 194, 269, 193, 268, 192, 267, 191, 266, 190, 265, 189, 264, 188, 263, 187, 262, 186, 261, 185, 260, 184, 259, 183, 258, 182, 257, 181, 256, 180, 255, 179, 254, 174, 172, 173, 178, 142, 144, 1211, 1298, 1242, 1330, 1244, 1332, 1213, 1300, 217, 219, 252, 253],
  .addRup 1726 #[Int.ofNat 1143, Int.negSucc 1143, Int.ofNat 15391] #[1496, 1497, 881, 288, 886, 325, 887, 326, 890, 290, 883],
  .addRup 1727 #[Int.negSucc 865, Int.negSucc 1142, Int.ofNat 15144] #[1493, 1495, 1496, 1497, 868, 139, 869, 202, 200, 137, 873, 875],
  .addRup 1728 #[Int.ofNat 15096, Int.negSucc 1142, Int.negSucc 1143, Int.ofNat 1699, Int.ofNat 15069, Int.ofNat 15658, Int.ofNat 130859, Int.ofNat 130861, Int.ofNat 130865] #[1493, 1494, 1496, 1498, 1503, 1506, 1508, 1510, 45, 925, 169, 1657, 496, 1656, 805, 167, 136, 46, 1655, 803, 1723, 47, 858, 48, 859, 860, 861, 862, 863, 864, 865, 866, 809, 867, 810, 1660, 812, 1661, 1662, 1722, 930, 1720, 932, 522, 926, 492],
  .addRup 1729 #[Int.negSucc 15070, Int.negSucc 1143, Int.ofNat 1699, Int.ofNat 15098, Int.ofNat 15393, Int.ofNat 130859, Int.ofNat 130861, Int.ofNat 130865] #[1493, 1494, 1495, 1496, 1497, 1498, 1502, 868, 1003, 142, 207, 1211, 203, 1242, 1243, 1246, 1215, 292, 327, 1726, 1727, 138, 1008, 1009, 1011, 1014, 1006, 431, 1728, 171, 140, 870, 205, 201, 200, 137, 873, 877, 874],
  .addRup 1730 #[Int.negSucc 23937, Int.negSucc 586, Int.negSucc 864] #[1493, 1494, 1495, 1497, 1501, 777, 1713, 778, 430, 913, 432, 491, 490, 489, 428, 784, 786],
  .addRup 1731 #[Int.negSucc 1142, Int.negSucc 1143, Int.ofNat 1699, Int.ofNat 15069, Int.ofNat 15096, Int.ofNat 23938, Int.ofNat 130859, Int.ofNat 130861, Int.ofNat 130865] #[1493, 1494, 1496, 1498, 1503, 1506, 1508, 1510, 45, 925, 1656, 805, 914, 1657, 496, 169, 431, 167, 136, 46, 1655, 803, 1723, 47, 858, 48, 859, 860, 861, 862, 863, 864, 865, 866, 809, 867, 810, 1660, 812, 1661, 1662, 1722, 930, 1720, 932, 522, 926, 492],
  .addRup 1732 #[Int.ofNat 15069, Int.negSucc 587, Int.negSucc 1143, Int.ofNat 1699, Int.ofNat 15097, Int.ofNat 15216, Int.ofNat 15245, Int.ofNat 130859, Int.ofNat 130861, Int.ofNat 130865] #[1493, 1494, 1495, 1496, 1497, 1500, 881, 175, 170, 176, 169, 140, 167, 1073, 136, 1105, 882, 1107, 1075, 215, 246, 244, 242, 211, 1730, 1731, 886, 888],
  .addRup 1733 #[Int.ofNat 1143, Int.negSucc 23642] #[1496, 1497, 881, 886, 888],
  .addRup 1734 #[Int.ofNat 15218, Int.negSucc 587, Int.negSucc 1143, Int.ofNat 15216, Int.negSucc 15243, Int.ofNat 27612, Int.ofNat 27615, Int.ofNat 130859, Int.ofNat 130861, Int.ofNat 130865] #[1493, 1494, 1495, 1496, 1497, 1498, 1500, 1503, 1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 45, 1059, 146, 221, 296, 147, 222, 297, 148, 223, 298, 149, 224, 299, 150, 225, 300, 151, 226, 301, 152, 227, 302, 153, 228, 303, 154, 229, 304, 155, 230, 305, 156, 231, 306, 157, 232, 307, 158, 233, 308, 159, 234, 309, 160, 235, 310, 161, 236, 311, 162, 237, 312, 163, 238, 313, 164, 239, 314, 165, 240, 315, 166, 241, 316, 199, 274, 349, 198, 273, 348, 197, 272, 347, 196, 271, 346, 195, 270, 345, 194, 269, 344, 193, 268, 343, 192, 267, 342, 191, 266, 341, 190, 265, 340, 189, 264, 339, 188, 263, 338, 187, 262, 337, 186, 261, 336, 185, 260, 335, 184, 259, 334, 183, 258, 333, 182, 257, 332, 181, 256, 331, 180, 255, 330, 179, 254, 329, 249, 248, 252, 1718, 1657, 1725, 253, 294, 219, 328, 1300, 1024, 1332, 496, 1064, 1330, 1066, 1298, 144, 178, 1729, 177, 1732, 138, 1019, 1060, 211, 492, 242, 522, 244, 1720, 246, 215, 1075, 1107, 1105, 1073, 140, 176, 168, 167, 136, 46, 1655, 803, 882, 858, 1733, 1656, 805, 47, 859, 48, 860, 861, 862, 863, 864, 865, 866, 809, 867, 810, 1660, 812, 1661, 1662, 1722, 1713, 1723, 914, 431],
  .addRup 1735 #[Int.negSucc 864, Int.negSucc 1142, Int.negSucc 1143, Int.ofNat 15393, Int.ofNat 15658, Int.ofNat 130859, Int.ofNat 130861, Int.ofNat 130865] #[1494, 1496, 1498, 1503, 1506, 1508, 1510, 45, 925, 46, 1655, 803, 1723, 1656, 805, 1657, 47, 858, 1658, 48, 859, 49, 860, 861, 862, 863, 864, 865, 866, 809, 867, 810, 1660, 812, 1661, 1662, 1721, 930, 931, 932, 934, 926, 928, 492, 496, 522, 1720],
  .addRup 1736 #[Int.negSucc 15243, Int.negSucc 587, Int.negSucc 1143, Int.ofNat 15216, Int.ofNat 27612, Int.ofNat 27614, Int.ofNat 27615, Int.ofNat 130859, Int.ofNat 130861, Int.ofNat 130865] #[1493, 1496, 1497, 1498, 1502, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 868, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 349, 348, 347, 346, 345, 344, 343, 342, 341, 340, 339, 338, 337, 336, 335, 334, 333, 332, 331, 330, 329, 1718, 1725, 294, 328, 1734, 217, 1213, 1021, 1245, 431, 1246, 1215, 292, 327, 1726, 1735, 136, 873, 167, 874, 875, 877, 869, 870, 138, 140, 169, 171],
  .addRup 1737 #[Int.ofNat 1423, Int.negSucc 586, Int.ofNat 1422, Int.negSucc 15094, Int.negSucc 15241, Int.negSucc 15538] #[1493, 1494, 1495, 1496, 1499, 1500, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 146, 221, 370, 147, 222, 371, 148, 223, 372, 149, 224, 373, 150, 225, 374, 151, 226, 375, 152, 227, 376, 153, 228, 377, 154, 229, 378, 155, 230, 379, 156, 231, 380, 157, 232, 381, 158, 233, 382, 159, 234, 383, 160, 235, 384, 161, 236, 385, 162, 237, 386, 163, 238, 387, 164, 239, 388, 165, 240, 389, 166, 241, 390, 199, 274, 423, 198, 273, 422, 197, 272, 421, 196, 271, 420, 195, 270, 419, 194, 269, 418, 193, 268, 417, 192, 267, 416, 191, 266, 415, 190, 265, 414, 189, 264, 413, 188, 263, 412, 187, 262, 411, 186, 261, 410, 185, 260, 409, 184, 259, 408, 183, 258, 407, 182, 257, 406, 181, 256, 405, 180, 255, 404, 179, 254, 403, 398, 219, 396, 397, 217, 253, 402, 368, 252, 369, 251, 215, 1075, 1262, 1353, 1107, 1268, 1359, 1105, 1265, 1356, 1073, 1264, 1355, 140, 1260, 1351, 176, 142, 144, 177, 178],
  .addRup 1738 #[Int.negSucc 586, Int.negSucc 864, Int.ofNat 1422, Int.negSucc 2798, Int.ofNat 15069, Int.negSucc 15538] #[1493, 1494, 1495, 1496, 1497, 1498, 1499, 1504, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 1003, 146, 370, 147, 371, 148, 372, 149, 373, 150, 374, 151, 375, 152, 376, 153, 377, 154, 378, 155, 379, 156, 380, 157, 381, 158, 382, 159, 383, 160, 384, 161, 385, 162, 386, 163, 387, 164, 388, 165, 389, 166, 390, 199, 423, 198, 422, 197, 421, 196, 420, 195, 419, 194, 418, 193, 417, 192, 416, 191, 415, 190, 414, 189, 413, 188, 412, 187, 411, 186, 410, 185, 409, 184, 408, 183, 407, 182, 406, 181, 405, 180, 404, 179, 403, 396, 175, 139, 402, 1008, 369, 1010, 1004, 213, 250, 1737, 1300, 1263, 1332, 1270, 1330, 1267, 1298, 1265, 144, 1264, 178, 1260, 142, 177, 176, 140, 1342, 1348, 1340, 1345, 1344],
  .addRup 1739 #[Int.ofNat 1422, Int.negSucc 864, Int.negSucc 2798, Int.ofNat 15069, Int.negSucc 15538] #[1493, 1495, 1497, 1498, 1499, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 1003, 221, 370, 222, 371, 223, 372, 224, 373, 225, 374, 226, 375, 227, 376, 228, 377, 229, 378, 230, 379, 231, 380, 232, 381, 233, 382, 234, 383, 235, 384, 236, 385, 237, 386, 238, 387, 239, 388, 240, 389, 241, 390, 274, 423, 273, 422, 272, 421, 271, 420, 270, 419, 269, 418, 268, 417, 267, 416, 266, 415, 265, 414, 264, 413, 263, 412, 262, 411, 261, 410, 260, 409, 259, 408, 258, 407, 257, 406, 256, 405, 255, 404, 254, 403, 249, 398, 217, 139, 397, 248, 1008, 368, 1010, 1004, 213, 1738, 211, 242, 244, 245, 246, 252, 215, 253, 1262, 219, 1269, 1263, 1270],
  .addRup 1740 #[Int.ofNat 15511, Int.negSucc 864, Int.ofNat 15069, Int.negSucc 15536, Int.ofNat 19653, Int.ofNat 23793] #[1493, 1494, 1496, 1497, 1498, 1499, 1502, 1503, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 1033, 146, 370, 501, 147, 371, 502, 148, 372, 503, 149, 373, 504, 150, 374, 505, 151, 375, 506, 152, 376, 507, 153, 377, 508, 154, 378, 509, 155, 379, 510, 156, 380, 511, 157, 381, 512, 158, 382, 513, 159, 383, 514, 160, 384, 515, 161, 385, 516, 162, 386, 517, 163, 387, 518, 164, 388, 519, 165, 389, 520, 166, 390, 521, 199, 423, 554, 198, 422, 553, 197, 421, 552, 196, 420, 551, 195, 419, 550, 194, 418, 549, 193, 417, 548, 192, 416, 547, 191, 415, 546, 190, 414, 545, 189, 413, 544, 188, 412, 543, 187, 411, 542, 186, 410, 541, 185, 409, 540, 184, 408, 539, 183, 407, 538, 182, 406, 537, 181, 405, 536, 180, 404, 535, 179, 403, 534, 398, 367, 395, 175, 1038, 396, 397, 1039, 402, 368, 1041, 369, 902, 768, 494, 492, 522, 524, 1043, 1045, 1037, 496, 526, 527, 533, 500, 1739, 1213, 1244, 1242, 1211, 142, 1249, 1253, 1254, 1256, 1257, 1259, 1251, 1252, 140, 144, 176, 178, 177],
  .addRup 1741 #[Int.negSucc 35597, Int.negSucc 15096, Int.negSucc 15390] #[1493, 1494, 1497, 1498, 1502, 1504, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 146, 296, 147, 297, 148, 298, 149, 299, 150, 300, 151, 301, 152, 302, 153, 303, 154, 304, 155, 305, 156, 306, 157, 307, 158, 308, 159, 309, 160, 310, 161, 311, 162, 312, 163, 313, 164, 314, 165, 315, 166, 316, 199, 349, 198, 348, 197, 347, 196, 346, 195, 345, 194, 344, 193, 343, 192, 342, 191, 341, 190, 340, 189, 339, 188, 338, 187, 337, 186, 336, 185, 335, 184, 334, 183, 333, 182, 332, 181, 331, 180, 330, 179, 329, 1244, 1245, 1242, 1246, 1211, 1215, 142, 292, 177, 327, 178, 328, 144, 294, 1298, 1302, 1330, 1334, 1331],
  .addRup 1742 #[Int.ofNat 15069, Int.negSucc 864, Int.negSucc 15536, Int.ofNat 19651, Int.ofNat 19653, Int.ofNat 23791, Int.ofNat 23793] #[1493, 1494, 1495, 1496, 1497, 1498, 1502, 1504, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 1016, 1003, 146, 221, 296, 147, 222, 297, 148, 223, 298, 149, 224, 299, 150, 225, 300, 151, 226, 301, 152, 227, 302, 153, 228, 303, 154, 229, 304, 155, 230, 305, 156, 231, 306, 157, 232, 307, 158, 233, 308, 159, 234, 309, 160, 235, 310, 161, 236, 311, 162, 237, 312, 163, 238, 313, 164, 239, 314, 165, 240, 315, 166, 241, 316, 199, 274, 349, 198, 273, 348, 197, 272, 347, 196, 271, 346, 195, 270, 345, 194, 269, 344, 193, 268, 343, 192, 267, 342, 191, 266, 341, 190, 265, 340, 189, 264, 339, 188, 263, 338, 187, 262, 337, 186, 261, 336, 185, 260, 335, 184, 259, 334, 183, 258, 333, 182, 257, 332, 181, 256, 331, 180, 255, 330, 179, 254, 329, 175, 139, 1008, 1009, 1010, 1012, 1004, 213, 1025, 250, 1026, 1029, 1740, 366, 1020, 766, 898, 1005, 215, 286, 288, 140, 251, 317, 319, 176, 320, 1741, 1213, 217, 252, 253, 219, 1300, 1332, 1333, 1330, 1334, 1298, 1302, 144, 294, 178, 328, 177, 327, 142, 292, 1211, 1215, 1242, 1246, 1243],
  .addRup 1743 #[Int.ofNat 15658, Int.negSucc 865, Int.ofNat 15245, Int.negSucc 15536, Int.ofNat 15686, Int.ofNat 23792] #[1494, 1495, 1497, 1498, 1499, 1501, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 1016, 1046, 777, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 423, 422, 421, 420, 419, 418, 417, 416, 415, 414, 413, 412, 411, 410, 409, 408, 407, 406, 405, 404, 403, 398, 460, 432, 1051, 1052, 1053, 1055, 1047, 427, 784, 456, 786, 458, 429, 900, 1048, 778, 368, 213, 1025, 211, 397, 1026, 242, 395, 1029, 244, 366, 1020, 246, 215],
  .addRup 1744 #[Int.negSucc 1698, Int.negSucc 1854, Int.ofNat 130869, Int.ofNat 130870, Int.ofNat 130871, Int.ofNat 130872, Int.ofNat 130874, Int.ofNat 130875, Int.ofNat 130876, Int.ofNat 130885, Int.ofNat 130886, Int.ofNat 130887, Int.ofNat 130891] #[94, 95, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 119, 121, 123, 125, 127, 1686, 102, 104, 106, 108, 110, 112, 114, 116, 124, 126, 128, 129, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1701, 1702, 1703, 131, 132, 133, 134, 1705, 135, 1706, 1707, 1708],
  .addRup 1745 #[Int.negSucc 1696, Int.negSucc 1697, Int.negSucc 1850, Int.negSucc 15830, Int.ofNat 130869, Int.ofNat 130870, Int.ofNat 130874, Int.ofNat 130875, Int.ofNat 130876, Int.ofNat 130885, Int.ofNat 130886, Int.ofNat 130887, Int.ofNat 130891] #[1498, 1503, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 1059, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 554, 553, 552, 551, 550, 549, 548, 547, 546, 545, 544, 543, 542, 541, 540, 539, 538, 537, 536, 535, 534, 529, 1685, 1684, 92, 93, 1744, 496, 1064, 526, 1065, 528, 1067, 498, 1070, 1062],
  .addRup 1746 #[Int.ofNat 1697, Int.negSucc 1697, Int.negSucc 15536] #[1498, 1499, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 1033, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 423, 422, 421, 420, 419, 418, 417, 416, 415, 414, 413, 412, 411, 410, 409, 408, 407, 406, 405, 404, 403, 398, 366, 1038, 395, 1039, 397, 368, 1036, 1041, 1044],
  .addRup 1747 #[Int.negSucc 15389, Int.ofNat 1974, Int.negSucc 2523, Int.negSucc 2798] #[1497, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 349, 348, 347, 346, 345, 344, 343, 342, 341, 340, 339, 338, 337, 336, 335, 334, 333, 332, 331, 330, 329, 324, 320, 292, 323, 327, 321, 328, 290, 294, 1273, 1274, 1281, 1280],
  .addRup 1748 #[Int.negSucc 15242, Int.ofNat 1422, Int.negSucc 2523, Int.negSucc 2798] #[1495, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 274, 273, 272, 271, 270, 269, 268, 267, 266, 265, 264, 263, 262, 261, 260, 259, 258, 257, 256, 255, 254, 249, 217, 245, 248, 252, 246, 253, 215, 219, 1262, 1263, 1270, 1269],
  .addRup 1749 #[Int.ofNat 15216, Int.negSucc 865, Int.ofNat 15243] #[1495, 1497, 1498, 1016, 244, 242, 211, 214, 1025, 1019, 1027],
  .addRup 1750 #[Int.ofNat 1698, Int.negSucc 865, Int.ofNat 15245, Int.negSucc 15536, Int.ofNat 15833, Int.ofNat 19800, Int.ofNat 23792, Int.ofNat 23940] #[1496, 1498, 1499, 1501, 1503, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 894, 1046, 370, 435, 371, 436, 372, 437, 373, 438, 374, 439, 375, 440, 376, 441, 377, 442, 378, 443, 379, 444, 380, 445, 381, 446, 382, 447, 383, 448, 384, 449, 385, 450, 386, 451, 387, 452, 388, 453, 389, 454, 390, 455, 423, 488, 422, 487, 421, 486, 420, 485, 419, 484, 418, 483, 417, 482, 416, 481, 415, 480, 414, 479, 413, 478, 412, 477, 411, 476, 410, 475, 409, 474, 408, 473, 407, 472, 406, 471, 405, 470, 404, 469, 403, 468, 398, 463, 431, 1051, 1743, 1052, 1053, 461, 462, 1054, 1047, 467, 433, 1056, 1057, 427, 434, 1058, 1049, 456, 783, 1050, 366, 492, 496, 395, 522, 526, 396, 397, 524, 402, 368, 494, 369, 900, 902, 1719, 910, 903, 908, 904, 906],
  .addRup 1751 #[Int.negSucc 1698, Int.negSucc 1854, Int.ofNat 130869, Int.ofNat 130870, Int.ofNat 130871, Int.ofNat 130872, Int.ofNat 130874, Int.ofNat 130875, Int.ofNat 130876, Int.ofNat 130885, Int.ofNat 130887, Int.ofNat 130891] #[94, 95, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 120, 1699, 1744],
  .addRup 1752 #[Int.negSucc 1419, Int.negSucc 865, Int.negSucc 1696, Int.negSucc 1697, Int.ofNat 15831, Int.ofNat 130885, Int.ofNat 130887, Int.ofNat 130891] #[1494, 1496, 1498, 1503, 1506, 1508, 1510, 89, 1059, 90, 1682, 937, 1683, 939, 91, 92, 993, 994, 93, 995, 996, 997, 998, 999, 1000, 1001, 944, 1002, 945, 1687, 947, 1688, 1689, 1685, 1684, 1751, 1064, 1065, 1066, 1068, 1060, 1061, 492, 494, 522, 524],
  .addRup 1753 #[Int.negSucc 865, Int.ofNat 1699, Int.ofNat 15243, Int.ofNat 15831] #[1498, 1503, 1059, 1749, 1064, 213, 1065, 1066, 1068, 1060, 1061, 492, 494, 522, 524],
  .addRup 1754 #[Int.negSucc 1972, Int.ofNat 1699, Int.ofNat 15831, Int.ofNat 19504, Int.ofNat 19651, Int.ofNat 23644, Int.ofNat 23791, Int.ofNat 35720] #[1493, 1494, 1495, 1496, 1498, 1499, 1500, 1502, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 894, 762, 146, 221, 147, 222, 148, 223, 149, 224, 150, 225, 151, 226, 152, 227, 153, 228, 154, 229, 155, 230, 156, 231, 157, 232, 158, 233, 159, 234, 160, 235, 161, 236, 162, 237, 163, 238, 164, 239, 165, 240, 166, 241, 199, 274, 198, 273, 197, 272, 196, 271, 195, 270, 194, 269, 193, 268, 192, 267, 191, 266, 190, 265, 189, 264, 188, 263, 187, 262, 186, 261, 185, 260, 184, 259, 183, 258, 182, 257, 181, 256, 180, 255, 179, 254, 174, 249, 1077, 883, 751, 1243, 1245, 1110, 364, 903, 362, 769, 1242, 1213, 1106, 1108, 904, 391, 770, 1211, 217, 1105, 1075, 906, 393, 772, 142, 248, 1073, 215, 908, 774, 173, 140, 246, 910, 776, 171, 1753, 138, 169, 1742, 167, 136],
  .addRup 1755 #[Int.ofNat 19651, Int.negSucc 1696, Int.ofNat 1699, Int.ofNat 23791, Int.ofNat 35720] #[1494, 1496, 1497, 1498, 1503, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 881, 749, 1059, 296, 501, 297, 502, 298, 503, 299, 504, 300, 505, 301, 506, 302, 507, 303, 508, 304, 509, 305, 510, 306, 511, 307, 512, 308, 513, 309, 514, 310, 515, 311, 516, 312, 517, 313, 518, 314, 519, 315, 520, 316, 521, 349, 554, 348, 553, 347, 552, 346, 551, 345, 550, 344, 549, 343, 548, 342, 547, 341, 546, 340, 545, 339, 544, 338, 543, 337, 542, 336, 541, 335, 540, 334, 539, 333, 538, 332, 537, 331, 536, 330, 535, 329, 534, 529, 766, 898, 496, 1064, 286, 754, 288, 886, 1065, 317, 755, 887, 1067, 319, 757, 758, 889, 890, 1070, 759, 891, 1062, 761, 893, 498, 528, 526, 1754, 290, 321, 322, 328, 294, 885, 753, 494, 492, 524, 522],
  .addRup 1756 #[Int.ofNat 866, Int.negSucc 1696, Int.negSucc 15093, Int.ofNat 15098] #[1493, 1498, 1003, 138, 1008, 169, 1009, 171, 140, 1012, 1005],
  .addRup 1757 #[Int.ofNat 35720, Int.negSucc 1696, Int.ofNat 1699, Int.negSucc 15093, Int.ofNat 15831] #[1493, 1494, 1495, 1496, 1498, 1502, 1503, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 1016, 1059, 146, 221, 147, 222, 148, 223, 149, 224, 150, 225, 151, 226, 152, 227, 153, 228, 154, 229, 155, 230, 156, 231, 157, 232, 158, 233, 159, 234, 160, 235, 161, 236, 162, 237, 163, 238, 164, 239, 165, 240, 166, 241, 199, 274, 198, 273, 197, 272, 196, 271, 195, 270, 194, 269, 193, 268, 192, 267, 191, 266, 190, 265, 189, 264, 188, 263, 187, 262, 186, 261, 185, 260, 184, 259, 183, 258, 182, 257, 181, 256, 180, 255, 179, 254, 174, 249, 1243, 1245, 1064, 1242, 1213, 1065, 1066, 1211, 217, 1068, 142, 248, 173, 1756, 1060, 492, 522, 524, 494, 1061, 213, 1025, 1749, 1026, 246, 1029, 215, 1020],
  .addRup 1758 #[Int.negSucc 1974, Int.negSucc 1696, Int.negSucc 15093, Int.ofNat 15831, Int.ofNat 23646, Int.ofNat 28224] #[1493, 1494, 1496, 1497, 1498, 1500, 1501, 1502, 1503, 1504, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 868, 1003, 1046, 1059, 925, 146, 296, 435, 501, 147, 297, 436, 502, 148, 298, 437, 503, 149, 299, 438, 504, 150, 300, 439, 505, 151, 301, 440, 506, 152, 302, 441, 507, 153, 303, 442, 508, 154, 304, 443, 509, 155, 305, 444, 510, 156, 306, 445, 511, 157, 307, 446, 512, 158, 308, 447, 513, 159, 309, 448, 514, 160, 310, 449, 515, 161, 311, 450, 516, 162, 312, 451, 517, 163, 313, 452, 518, 164, 314, 453, 519, 165, 315, 454, 520, 166, 316, 455, 521, 199, 349, 488, 554, 198, 348, 487, 553, 197, 347, 486, 552, 196, 346, 485, 551, 195, 345, 484, 550, 194, 344, 483, 549, 193, 343, 482, 548, 192, 342, 481, 547, 191, 341, 480, 546, 190, 340, 479, 545, 189, 339, 478, 544, 188, 338, 477, 543, 187, 337, 476, 542, 186, 336, 475, 541, 185, 335, 474, 540, 184, 334, 473, 539, 183, 333, 472, 538, 182, 332, 471, 537, 181, 331, 470, 536, 180, 330, 469, 535, 179, 329, 468, 534, 324, 1302, 885, 1334, 494, 930, 1331, 530, 524, 932, 1330, 522, 1298, 492, 144, 1060, 926, 178, 138, 1008, 873, 172, 169, 1009, 874, 171, 170, 1011, 876, 877, 140, 177, 1014, 879, 1073, 870, 142, 1105, 1714, 1211, 871, 1006, 1106, 898, 1242, 429, 431, 1051, 1110, 288, 1243, 464, 1052, 1077, 1246, 465, 1054, 290, 1215, 1056, 1057, 292, 1058, 1049, 323, 433, 321, 466, 319, 467, 317, 434, 286, 1050, 1271, 496, 1064, 1275, 531, 1065, 1276, 1067, 1278, 1070, 1281, 1062, 1274, 498, 500, 532, 533],
  .addRup 1759 #[Int.ofNat 866, Int.negSucc 587, Int.negSucc 1696, Int.negSucc 1972, Int.ofNat 1974, Int.ofNat 1975, Int.negSucc 15093, Int.ofNat 15510, Int.ofNat 15831, Int.ofNat 23327, Int.ofNat 23328] #[1493, 1494, 1495, 1496, 1498, 1499, 1500, 1501, 1503, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 1, 1003, 1046, 146, 370, 435, 147, 371, 436, 148, 372, 437, 149, 373, 438, 150, 374, 439, 151, 375, 440, 152, 376, 441, 153, 377, 442, 154, 378, 443, 155, 379, 444, 156, 380, 445, 157, 381, 446, 158, 382, 447, 159, 383, 448, 160, 384, 449, 161, 385, 450, 162, 386, 451, 163, 387, 452, 164, 388, 453, 165, 389, 454, 166, 390, 455, 199, 423, 488, 198, 422, 487, 197, 421, 486, 196, 420, 485, 195, 419, 484, 194, 418, 483, 193, 417, 482, 192, 416, 481, 191, 415, 480, 190, 414, 479, 189, 413, 478, 188, 412, 477, 187, 411, 476, 186, 410, 475, 185, 409, 474, 184, 408, 473, 183, 407, 472, 182, 406, 471, 181, 405, 470, 180, 404, 469, 179, 403, 468, 174, 463, 138, 1008, 1077, 1629, 672, 169, 1009, 1110, 1011, 1106, 1108, 1014, 1105, 1075, 1073, 215, 140, 171, 172, 173, 1725, 178, 142, 251, 144, 1006, 871, 1271, 243, 872, 1362, 431, 1051, 429, 1275, 242, 494, 1366, 1052, 1276, 211, 524, 1367, 1054, 1279, 2, 1628, 670, 522, 1370, 1273, 3, 726, 492, 1364, 368, 727, 1632, 369, 728, 402, 729, 401, 730, 394, 731, 732, 393, 733, 734, 677, 391, 735, 678, 1633, 362, 680, 1634, 1630, 4, 1635, 1057, 1049, 433, 462, 460, 458, 456, 427, 1631, 5, 6, 7, 8, 9, 10, 11, 12, 13, 1636, 14, 15, 1637, 16, 17, 1638, 18, 19, 1639, 20, 21, 1640, 22, 23, 1641, 24, 25, 1642, 26, 27, 1643, 28, 29, 1644, 30, 31, 1645, 32, 33, 1646, 34, 35, 1647, 36, 37, 1648, 38, 39, 1649, 40, 41, 1650, 42, 43, 1651, 44, 1652, 1653, 1654],
  .addRup 1760 #[Int.negSucc 19650, Int.ofNat 1699, Int.ofNat 15831, Int.ofNat 23791] #[1493, 1494, 1495, 1496, 1497, 1498, 1500, 1502, 1503, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 868, 881, 1059, 146, 221, 296, 147, 222, 297, 148, 223, 298, 149, 224, 299, 150, 225, 300, 151, 226, 301, 152, 227, 302, 153, 228, 303, 154, 229, 304, 155, 230, 305, 156, 231, 306, 157, 232, 307, 158, 233, 308, 159, 234, 309, 160, 235, 310, 161, 236, 311, 162, 237, 312, 163, 238, 313, 164, 239, 314, 165, 240, 315, 166, 241, 316, 199, 274, 349, 198, 273, 348, 197, 272, 347, 196, 271, 346, 195, 270, 345, 194, 269, 344, 193, 268, 343, 192, 267, 342, 191, 266, 341, 190, 265, 340, 189, 264, 339, 188, 263, 338, 187, 262, 337, 186, 261, 336, 185, 260, 335, 184, 259, 334, 183, 258, 333, 182, 257, 332, 181, 256, 331, 180, 255, 330, 179, 254, 329, 249, 1064, 1065, 1066, 1068, 764, 765, 898, 288, 1733, 886, 325, 882, 887, 136, 873, 889, 890, 167, 874, 891, 168, 876, 893, 878, 879, 880, 1757, 1246, 1215, 292, 1758, 294, 328, 327, 326, 290, 1077, 883, 1110, 364, 1106, 1108, 1105, 1075, 1073, 215, 140, 176, 1759, 1060, 492, 522, 524, 494, 1061, 872, 213, 144, 1749, 178, 246, 177, 248, 142, 217, 1211, 1213, 1242, 1244],
  .addRup 1761 #[Int.negSucc 1696, Int.ofNat 1699, Int.ofNat 15831, Int.ofNat 23791] #[1494, 1496, 1497, 1498, 1502, 1503, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 881, 749, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 349, 348, 347, 346, 345, 344, 343, 342, 341, 340, 339, 338, 337, 336, 335, 334, 333, 332, 331, 330, 329, 898, 288, 886, 887, 889, 891, 893, 1760, 766, 286, 754, 317, 755, 319, 757, 320, 759, 761, 1755, 1246, 1215, 292, 327, 328, 294, 885, 753, 494, 492, 524, 522],
  .addRup 1762 #[Int.negSucc 1142, Int.negSucc 1420, Int.negSucc 1421, Int.negSucc 1974, Int.negSucc 15831] #[1496, 1498, 1500, 1502, 1503, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 554, 553, 552, 551, 550, 549, 548, 547, 546, 545, 544, 543, 542, 541, 540, 539, 538, 537, 536, 535, 534, 1140, 1272, 1213, 1075, 1245, 1108, 1246, 1110, 1215, 1077, 1277, 1148, 1149, 1153, 1144, 498, 532, 533, 500, 1278, 1274, 1281],
  .addRup 1763 #[Int.negSucc 1974, Int.negSucc 1145, Int.negSucc 15242, Int.negSucc 15831] #[1493, 1494, 1495, 1496, 1497, 1498, 1500, 1502, 1504, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 146, 221, 147, 222, 148, 223, 149, 224, 150, 225, 151, 226, 152, 227, 153, 228, 154, 229, 155, 230, 156, 231, 157, 232, 158, 233, 159, 234, 160, 235, 161, 236, 162, 237, 163, 238, 164, 239, 165, 240, 166, 241, 199, 274, 198, 273, 197, 272, 196, 271, 195, 270, 194, 269, 193, 268, 192, 267, 191, 266, 190, 265, 189, 264, 188, 263, 187, 262, 186, 261, 185, 260, 184, 259, 183, 258, 182, 257, 181, 256, 180, 255, 179, 254, 1302, 245, 1334, 1716, 1331, 1333, 1330, 1300, 1298, 219, 144, 253, 178, 247, 252, 246, 217, 215, 1213, 1075, 1244, 1107, 1108, 1242, 1105, 1110, 1211, 1073, 1077, 142, 140, 290, 177, 321, 176, 168, 167, 136, 1762, 288, 1733, 319, 882, 317, 286],
  .addRup 1764 #[Int.negSucc 31457, Int.ofNat 1143, Int.negSucc 1145, Int.ofNat 15392, Int.ofNat 15393] #[1493, 1494, 1496, 1497, 1498, 1500, 1502, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 868, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 199, 198, 197, 196, 195, 194, 193, 192, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 1107, 1108, 288, 1733, 1105, 1110, 325, 1073, 1077, 140, 290, 321, 326, 319, 327, 317, 292, 286, 1215, 882, 1246, 136, 873, 1243, 167, 874, 1242, 168, 876, 1211, 176, 878, 142, 177, 880, 178, 872, 144],
  .addRup 1765 #[Int.ofNat 1143, Int.negSucc 1145, Int.negSucc 15242, Int.ofNat 15393] #[1493, 1494, 1495, 1496, 1497, 1498, 1500, 1502, 1504, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 146, 221, 147, 222, 148, 223, 149, 224, 150, 225, 151, 226, 152, 227, 153, 228, 154, 229, 155, 230, 156, 231, 157, 232, 158, 233, 159, 234, 160, 235, 161, 236, 162, 237, 163, 238, 164, 239, 165, 240, 166, 241, 199, 274, 198, 273, 197, 272, 196, 271, 195, 270, 194, 269, 193, 268, 192, 267, 191, 266, 190, 265, 189, 264, 188, 263, 187, 262, 186, 261, 185, 260, 184, 259, 183, 258, 182, 257, 181, 256, 180, 255, 179, 254, 249, 288, 1733, 322, 325, 1764, 1075, 215, 246, 247, 248, 253, 217, 219, 1213, 1300, 1244, 1245, 1332, 1242, 1246, 1330, 1211, 1215, 1298, 142, 292, 144, 327, 178, 320, 326, 177, 319, 290, 317, 1077, 286, 1110, 882, 1106, 136, 1105, 167, 1073, 168, 140, 176],
  .addRup 1766 #[Int.negSucc 1972, Int.negSucc 15362, Int.ofNat 15511, Int.ofNat 36041, Int.ofNat 40181] #[1493, 1494, 1497, 1499, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 749, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 423, 422, 421, 420, 419, 418, 417, 416, 415, 414, 413, 412, 411, 410, 409, 408, 407, 406, 405, 404, 403, 291, 1364, 1273, 354, 369, 368, 352, 402, 350, 401, 287, 400, 754, 392, 755, 391, 758, 362, 751],
  .addRup 1767 #[Int.negSucc 1364, Int.negSucc 587, Int.negSucc 1143, Int.ofNat 15216, Int.negSucc 15243, Int.ofNat 27612, Int.ofNat 27614, Int.ofNat 27615] #[70, 71, 72, 1671, 74, 75, 76, 1673, 78, 80, 83, 1677, 1736],
  .addRup 1768 #[Int.negSucc 1143, Int.negSucc 587, Int.negSucc 1142, Int.negSucc 1145, Int.ofNat 15216, Int.negSucc 15243, Int.ofNat 15658, Int.negSucc 15681, Int.ofNat 27612, Int.ofNat 27614, Int.ofNat 27615] #[1493, 1496, 45, 868, 1719, 1767, 1725, 68, 66, 64, 62, 60, 58, 56, 54, 53, 52, 51, 50, 49, 48, 47, 46, 136, 873, 167, 874, 875, 877, 869, 870, 138, 140, 169, 171],
  .addRup 1769 #[Int.negSucc 15244, Int.negSucc 1142, Int.negSucc 1145, Int.ofNat 1697, Int.ofNat 1975, Int.ofNat 15216, Int.negSucc 15243, Int.ofNat 19358, Int.ofNat 27612, Int.ofNat 27614, Int.ofNat 27615] #[1494, 1495, 1496, 1497, 1498, 1499, 1501, 1502, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 894, 777, 221, 296, 370, 435, 222, 297, 371, 436, 223, 298, 372, 437, 224, 299, 373, 438, 225, 300, 374, 439, 226, 301, 375, 440, 227, 302, 376, 441, 228, 303, 377, 442, 229, 304, 378, 443, 230, 305, 379, 444, 231, 306, 380, 445, 232, 307, 381, 446, 233, 308, 382, 447, 234, 309, 383, 448, 235, 310, 384, 449, 236, 311, 385, 450, 237, 312, 386, 451, 238, 313, 387, 452, 239, 314, 388, 453, 240, 315, 389, 454, 241, 316, 390, 455, 274, 349, 423, 488, 273, 348, 422, 487, 272, 347, 421, 486, 271, 346, 420, 485, 270, 345, 419, 484, 269, 344, 418, 483, 268, 343, 417, 482, 267, 342, 416, 481, 266, 341, 415, 480, 265, 340, 414, 479, 264, 339, 413, 478, 263, 338, 412, 477, 262, 337, 411, 476, 261, 336, 410, 475, 260, 335, 409, 474, 259, 334, 408, 473, 258, 333, 407, 472, 257, 332, 406, 471, 256, 331, 405, 470, 255, 330, 404, 469, 254, 329, 403, 468, 249, 463, 366, 247, 248, 289, 294, 253, 217, 328, 219, 1213, 739, 1363, 1245, 427, 784, 1368, 1246, 456, 785, 1370, 1215, 787, 292, 790, 327, 1272, 1021, 431, 1277, 1279, 1766, 290, 326, 318, 317, 286, 1768, 364, 903, 399, 904, 400, 906, 908, 909, 910, 902, 369, 402, 396, 401, 395, 368, 393, 900, 391, 429, 362, 458, 780, 460, 433, 462],
  .addRup 1770 #[Int.negSucc 586, Int.ofNat 741] #[1494, 1, 2],
  .addRup 1771 #[Int.negSucc 864, Int.ofNat 1296] #[1496, 45, 46],
  .addRup 1772 #[Int.negSucc 865, Int.ofNat 1849] #[1498, 89, 90],
  .addRup 1773 #[Int.ofNat 15069, Int.negSucc 865] #[1497, 139],
  .addRup 1774 #[Int.ofNat 15070, Int.negSucc 866] #[1499, 141],
  .addRup 1775 #[Int.ofNat 15071, Int.negSucc 867] #[1501, 143],
  .addRup 1776 #[Int.ofNat 15072, Int.negSucc 868] #[1503, 145],
  .addRup 1777 #[Int.ofNat 15068, Int.ofNat 15094] #[1493, 167],
  .addRup 1778 #[Int.negSucc 15093, Int.ofNat 15095] #[1493, 168],
  .addRup 1779 #[Int.ofNat 15069, Int.negSucc 15093, Int.ofNat 15096] #[1493, 169],
  .addRup 1780 #[Int.negSucc 15095, Int.ofNat 15097] #[1493, 170],
  .addRup 1781 #[Int.negSucc 15095, Int.ofNat 15070, Int.ofNat 15098] #[1493, 171],
  .addRup 1782 #[Int.negSucc 15097, Int.ofNat 15099] #[1493, 172],
  .addRup 1783 #[Int.ofNat 15071, Int.negSucc 15097] #[1493, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 199, 198, 197, 196, 195, 194, 193, 192, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 174, 173],
  .addRup 1784 #[Int.ofNat 15069, Int.ofNat 15095] #[1493, 175],
  .addRup 1785 #[Int.negSucc 15094, Int.ofNat 15070, Int.ofNat 15097] #[1493, 176],
  .addRup 1786 #[Int.ofNat 15099, Int.ofNat 15071, Int.negSucc 15096] #[1493, 177],
  .addRup 1787 #[Int.ofNat 15072, Int.negSucc 15098] #[1493, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 199, 198, 197, 196, 195, 194, 193, 192, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178],
  .addRup 1788 #[Int.negSucc 15143, Int.ofNat 15145] #[1493, 203],
  .addRup 1789 #[Int.negSucc 15069, Int.negSucc 15143] #[1493, 204],
  .addRup 1790 #[Int.negSucc 15144, Int.ofNat 15147] #[1493, 206],
  .addRup 1791 #[Int.negSucc 15070, Int.negSucc 15144] #[1493, 207],
  .addRup 1792 #[Int.negSucc 15069, Int.ofNat 15146] #[1493, 208],
  .addRup 1793 #[Int.ofNat 15147, Int.negSucc 15070, Int.negSucc 15145] #[1493, 209],
  .addRup 1794 #[Int.negSucc 15071, Int.negSucc 15146] #[1493, 210],
  .addRup 1795 #[Int.ofNat 15215, Int.negSucc 586] #[1493, 212],
  .addRup 1796 #[Int.ofNat 15217, Int.negSucc 1420] #[1499, 216],
  .addRup 1797 #[Int.ofNat 15218, Int.negSucc 1421] #[1501, 218],
  .addRup 1798 #[Int.ofNat 15219, Int.negSucc 1422] #[1503, 220],
  .addRup 1799 #[Int.ofNat 15215, Int.ofNat 15241] #[1495, 242],
  .addRup 1800 #[Int.negSucc 15240, Int.ofNat 15242] #[1495, 243],
  .addRup 1801 #[Int.negSucc 15240, Int.ofNat 15216, Int.ofNat 15243] #[1495, 244],
  .addRup 1802 #[Int.negSucc 15242, Int.ofNat 15244] #[1495, 245],
  .addRup 1803 #[Int.ofNat 15245, Int.ofNat 15217, Int.negSucc 15242] #[1495, 246],
  .addRup 1804 #[Int.negSucc 15244, Int.ofNat 15246] #[1495, 247],
  .addRup 1805 #[Int.ofNat 15218, Int.negSucc 15244] #[1495, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 274, 273, 272, 271, 270, 269, 268, 267, 266, 265, 264, 263, 262, 261, 260, 259, 258, 257, 256, 255, 254, 249, 248],
  .addRup 1806 #[Int.ofNat 15216, Int.ofNat 15242] #[1495, 250],
  .addRup 1807 #[Int.ofNat 15244, Int.ofNat 15217, Int.negSucc 15241] #[1495, 251],
  .addRup 1808 #[Int.ofNat 15218, Int.negSucc 15243, Int.ofNat 15246] #[1495, 252],
  .addRup 1809 #[Int.ofNat 15219, Int.negSucc 15245] #[1495, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 274, 273, 272, 271, 270, 269, 268, 267, 266, 265, 264, 263, 262, 261, 260, 259, 258, 257, 256, 255, 254, 253],
  .addRup 1810 #[Int.negSucc 15214, Int.ofNat 15289] #[1495, 275],
  .addRup 1811 #[Int.negSucc 15288, Int.negSucc 15215, Int.ofNat 15291] #[1495, 276],
  .addRup 1812 #[Int.negSucc 15290, Int.ofNat 15292] #[1495, 277],
  .addRup 1813 #[Int.negSucc 15216, Int.negSucc 15290] #[1495, 278],
  .addRup 1814 #[Int.negSucc 15215, Int.ofNat 15290] #[1495, 279],
  .addRup 1815 #[Int.negSucc 15216, Int.negSucc 15289, Int.ofNat 15292] #[1495, 280],
  .addRup 1816 #[Int.negSucc 15291, Int.ofNat 15294] #[1495, 281],
  .addRup 1817 #[Int.negSucc 15217, Int.negSucc 15291] #[1495, 282],
  .addRup 1818 #[Int.negSucc 15216, Int.ofNat 15293] #[1495, 283],
  .addRup 1819 #[Int.ofNat 15294, Int.negSucc 15217, Int.negSucc 15292] #[1495, 284],
  .addRup 1820 #[Int.negSucc 15218, Int.negSucc 15293] #[1495, 285],
  .addRup 1821 #[Int.ofNat 15362, Int.negSucc 587] #[1493, 287],
  .addRup 1822 #[Int.ofNat 15363, Int.negSucc 1142] #[1495, 289],
  .addRup 1823 #[Int.ofNat 15364, Int.negSucc 1972] #[1499, 291],
  .addRup 1824 #[Int.ofNat 15365, Int.negSucc 1973] #[1501, 293],
  .addRup 1825 #[Int.ofNat 15366, Int.negSucc 1974] #[1503, 295],
  .addRup 1826 #[Int.ofNat 15362, Int.ofNat 15388] #[1497, 317],
  .addRup 1827 #[Int.negSucc 15387, Int.ofNat 15389] #[1497, 318],
  .addRup 1828 #[Int.negSucc 15387, Int.ofNat 15363, Int.ofNat 15390] #[1497, 319],
  .addRup 1829 #[Int.negSucc 15389, Int.ofNat 15391] #[1497, 320],
  .addRup 1830 #[Int.ofNat 15364, Int.negSucc 15389, Int.ofNat 15392] #[1497, 321],
  .addRup 1831 #[Int.negSucc 15391, Int.ofNat 15393] #[1497, 322],
  .addRup 1832 #[Int.ofNat 15365, Int.negSucc 15391] #[1497, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 349, 348, 347, 346, 345, 344, 343, 342, 341, 340, 339, 338, 337, 336, 335, 334, 333, 332, 331, 330, 329, 324, 323],
  .addRup 1833 #[Int.ofNat 15363, Int.ofNat 15389] #[1497, 325],
  .addRup 1834 #[Int.negSucc 15388, Int.ofNat 15364, Int.ofNat 15391] #[1497, 326],
  .addRup 1835 #[Int.negSucc 15390, Int.ofNat 15365, Int.ofNat 15393] #[1497, 327],
  .addRup 1836 #[Int.ofNat 15366, Int.negSucc 15392] #[1497, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 349, 348, 347, 346, 345, 344, 343, 342, 341, 340, 339, 338, 337, 336, 335, 334, 333, 332, 331, 330, 329, 328],
  .addRup 1837 #[Int.negSucc 15361, Int.ofNat 15436] #[1497, 350],
  .addRup 1838 #[Int.negSucc 15435, Int.ofNat 15437] #[1497, 351],
  .addRup 1839 #[Int.negSucc 15435, Int.negSucc 15362, Int.ofNat 15438] #[1497, 352],
  .addRup 1840 #[Int.negSucc 15437, Int.ofNat 15439] #[1497, 353],
  .addRup 1841 #[Int.negSucc 15363, Int.negSucc 15437] #[1497, 354],
  .addRup 1842 #[Int.negSucc 15436, Int.ofNat 15440] #[1497, 355],
  .addRup 1843 #[Int.ofNat 15439, Int.negSucc 15363, Int.negSucc 15436] #[1497, 356],
  .addRup 1844 #[Int.negSucc 15438, Int.ofNat 15441] #[1497, 357],
  .addRup 1845 #[Int.negSucc 15364, Int.negSucc 15438] #[1497, 358],
  .addRup 1846 #[Int.negSucc 15363, Int.ofNat 15440] #[1497, 359],
  .addRup 1847 #[Int.ofNat 15441, Int.negSucc 15364, Int.negSucc 15439] #[1497, 360],
  .addRup 1848 #[Int.negSucc 15365, Int.negSucc 15440] #[1497, 361],
  .addRup 1849 #[Int.ofNat 15509, Int.negSucc 588] #[1493, 363],
  .addRup 1850 #[Int.ofNat 15510, Int.negSucc 1143] #[1495, 365],
  .addRup 1851 #[Int.ofNat 15511, Int.negSucc 1696] #[1497, 367],
  .addRup 1852 #[Int.ofNat 15509, Int.ofNat 15535] #[1499, 391],
  .addRup 1853 #[Int.negSucc 15534, Int.ofNat 15536] #[1499, 392],
  .addRup 1854 #[Int.ofNat 15510, Int.negSucc 15534, Int.ofNat 15537] #[1499, 393],
  .addRup 1855 #[Int.negSucc 15536, Int.ofNat 15538] #[1499, 394],
  .addRup 1856 #[Int.ofNat 15539, Int.ofNat 15511, Int.negSucc 15536] #[1499, 395],
  .addRup 1857 #[Int.negSucc 15538, Int.ofNat 15540] #[1499, 396],
  .addRup 1858 #[Int.ofNat 15512, Int.negSucc 15538] #[1499, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 423, 422, 421, 420, 419, 418, 417, 416, 415, 414, 413, 412, 411, 410, 409, 408, 407, 406, 405, 404, 403, 398, 397],
  .addRup 1859 #[Int.ofNat 15510, Int.ofNat 15536] #[1499, 399],
  .addRup 1860 #[Int.ofNat 15538, Int.ofNat 15511, Int.negSucc 15535] #[1499, 400],
  .addRup 1861 #[Int.ofNat 15540, Int.ofNat 15512, Int.negSucc 15537] #[1499, 401],
  .addRup 1862 #[Int.ofNat 15513, Int.negSucc 15539] #[1499, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 423, 422, 421, 420, 419, 418, 417, 416, 415, 414, 413, 412, 411, 410, 409, 408, 407, 406, 405, 404, 403, 402],
  .addRup 1863 #[Int.negSucc 15508, Int.ofNat 15583] #[1499, 424],
  .addRup 1864 #[Int.ofNat 15585, Int.negSucc 15509, Int.negSucc 15582] #[1499, 425],
  .addRup 1865 #[Int.negSucc 15510, Int.negSucc 15584] #[1499, 426],
  .addRup 1866 #[Int.ofNat 15656, Int.negSucc 589] #[1493, 428],
  .addRup 1867 #[Int.ofNat 15657, Int.negSucc 1144] #[1495, 430],
  .addRup 1868 #[Int.ofNat 15658, Int.negSucc 1697] #[1497, 432],
  .addRup 1869 #[Int.ofNat 15656, Int.ofNat 15682] #[1501, 456],
  .addRup 1870 #[Int.negSucc 15681, Int.ofNat 15683] #[1501, 457],
  .addRup 1871 #[Int.ofNat 15684, Int.ofNat 15657, Int.negSucc 15681] #[1501, 458],
  .addRup 1872 #[Int.negSucc 15683, Int.ofNat 15685] #[1501, 459],
  .addRup 1873 #[Int.ofNat 15686, Int.ofNat 15658, Int.negSucc 15683] #[1501, 460],
  .addRup 1874 #[Int.negSucc 15685, Int.ofNat 15687] #[1501, 461],
  .addRup 1875 #[Int.ofNat 15659, Int.negSucc 15685] #[1501, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 488, 487, 486, 485, 484, 483, 482, 481, 480, 479, 478, 477, 476, 475, 474, 473, 472, 471, 470, 469, 468, 463, 462],
  .addRup 1876 #[Int.ofNat 15657, Int.ofNat 15683] #[1501, 464],
  .addRup 1877 #[Int.ofNat 15685, Int.ofNat 15658, Int.negSucc 15682] #[1501, 465],
  .addRup 1878 #[Int.ofNat 15687, Int.ofNat 15659, Int.negSucc 15684] #[1501, 466],
  .addRup 1879 #[Int.ofNat 15660, Int.negSucc 15686] #[1501, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 488, 487, 486, 485, 484, 483, 482, 481, 480, 479, 478, 477, 476, 475, 474, 473, 472, 471, 470, 469, 468, 467],
  .addRup 1880 #[Int.negSucc 15655, Int.ofNat 15730] #[1501, 489],
  .addRup 1881 #[Int.negSucc 15729, Int.negSucc 15656, Int.ofNat 15732] #[1501, 490],
  .addRup 1882 #[Int.negSucc 15657, Int.negSucc 15731] #[1501, 491],
  .addRup 1883 #[Int.ofNat 15803, Int.negSucc 590] #[1493, 493],
  .addRup 1884 #[Int.ofNat 15804, Int.negSucc 1145] #[1495, 495],
  .addRup 1885 #[Int.ofNat 15805, Int.negSucc 1698] #[1497, 497],
  .addRup 1886 #[Int.ofNat 15806, Int.negSucc 2249] #[1499, 499],
  .addRup 1887 #[Int.ofNat 15803, Int.ofNat 15829] #[1503, 522],
  .addRup 1888 #[Int.negSucc 15828, Int.ofNat 15830] #[1503, 523],
  .addRup 1889 #[Int.negSucc 15828, Int.ofNat 15804, Int.ofNat 15831] #[1503, 524],
  .addRup 1890 #[Int.negSucc 15830, Int.ofNat 15832] #[1503, 525],
  .addRup 1891 #[Int.ofNat 15833, Int.ofNat 15805, Int.negSucc 15830] #[1503, 526],
  .addRup 1892 #[Int.negSucc 15832, Int.ofNat 15834] #[1503, 527],
  .addRup 1893 #[Int.ofNat 15806, Int.negSucc 15832] #[1503, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 554, 553, 552, 551, 550, 549, 548, 547, 546, 545, 544, 543, 542, 541, 540, 539, 538, 537, 536, 535, 534, 529, 528],
  .addRup 1894 #[Int.ofNat 15804, Int.ofNat 15830] #[1503, 530],
  .addRup 1895 #[Int.ofNat 15832, Int.ofNat 15805, Int.negSucc 15829] #[1503, 531],
  .addRup 1896 #[Int.ofNat 15834, Int.ofNat 15806, Int.negSucc 15831] #[1503, 532],
  .addRup 1897 #[Int.ofNat 15807, Int.negSucc 15833] #[1503, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 554, 553, 552, 551, 550, 549, 548, 547, 546, 545, 544, 543, 542, 541, 540, 539, 538, 537, 536, 535, 534, 533],
  .addRup 1898 #[Int.negSucc 15802, Int.ofNat 15877] #[1503, 555],
  .addRup 1899 #[Int.negSucc 15876, Int.ofNat 15878] #[1503, 556],
  .addRup 1900 #[Int.negSucc 15876, Int.negSucc 15803, Int.ofNat 15879] #[1503, 557],
  .addRup 1901 #[Int.negSucc 15804, Int.negSucc 15878] #[1503, 558],
  .addRup 1902 #[Int.negSucc 15803, Int.ofNat 15878] #[1503, 559],
  .addRup 1903 #[Int.negSucc 15877, Int.ofNat 15881] #[1503, 560],
  .addRup 1904 #[Int.negSucc 15877, Int.negSucc 15804, Int.ofNat 15880] #[1503, 561],
  .addRup 1905 #[Int.negSucc 15879, Int.ofNat 15882] #[1503, 562],
  .addRup 1906 #[Int.negSucc 15805, Int.negSucc 15879] #[1503, 563],
  .addRup 1907 #[Int.negSucc 15804, Int.ofNat 15881] #[1503, 564],
  .addRup 1908 #[Int.ofNat 15882, Int.negSucc 15805, Int.negSucc 15880] #[1503, 565],
  .addRup 1909 #[Int.negSucc 15806, Int.negSucc 15881] #[1503, 566],
  .addRup 1910 #[Int.ofNat 15953, Int.negSucc 2250] #[1499, 571],
  .addRup 1911 #[Int.ofNat 15954, Int.negSucc 2799] #[1501, 573],
  .addRup 1912 #[Int.ofNat 15955, Int.negSucc 3346] #[1503, 575],
  .addRup 1913 #[Int.ofNat 15952, Int.ofNat 15950, Int.ofNat 15951, Int.ofNat 15953, Int.ofNat 15954, Int.ofNat 15955] #[1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596],
  .addRup 1914 #[Int.negSucc 15952, Int.ofNat 16075] #[1505, 597],
  .addRup 1915 #[Int.negSucc 16074, Int.ofNat 16076] #[1505, 598],
  .addRup 1916 #[Int.negSucc 15953, Int.ofNat 16076] #[1505, 599],
  .addRup 1917 #[Int.negSucc 15954, Int.negSucc 16075] #[1505, 600],
  .addRup 1918 #[Int.ofNat 16100, Int.negSucc 2251] #[1499, 605],
  .addRup 1919 #[Int.ofNat 16101, Int.negSucc 2800] #[1501, 607],
  .addRup 1920 #[Int.ofNat 16102, Int.negSucc 3347] #[1503, 609],
  .addRup 1921 #[Int.ofNat 16099, Int.ofNat 16097, Int.ofNat 16098, Int.ofNat 16100, Int.ofNat 16101, Int.ofNat 16102] #[1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630],
  .addRup 1922 #[Int.negSucc 16099, Int.ofNat 16222] #[1507, 631],
  .addRup 1923 #[Int.negSucc 16221, Int.ofNat 16223] #[1507, 632],
  .addRup 1924 #[Int.negSucc 16100, Int.ofNat 16223] #[1507, 633],
  .addRup 1925 #[Int.negSucc 16101, Int.negSucc 16222] #[1507, 634],
  .addRup 1926 #[Int.ofNat 16247, Int.negSucc 2252] #[1499, 639],
  .addRup 1927 #[Int.ofNat 16248, Int.negSucc 2801] #[1501, 641],
  .addRup 1928 #[Int.ofNat 16249, Int.negSucc 3348] #[1503, 643],
  .addRup 1929 #[Int.ofNat 16246, Int.ofNat 16244, Int.ofNat 16245, Int.ofNat 16247, Int.ofNat 16248, Int.ofNat 16249] #[1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1521, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541, 1543, 1545, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664],
  .addRup 1930 #[Int.negSucc 16246, Int.ofNat 16369] #[1509, 665],
  .addRup 1931 #[Int.negSucc 16368, Int.ofNat 16370] #[1509, 666],
  .addRup 1932 #[Int.negSucc 16247, Int.ofNat 16370] #[1509, 667],
  .addRup 1933 #[Int.negSucc 16248, Int.negSucc 16369] #[1509, 668],
  .addRup 1934 #[Int.ofNat 19037, Int.negSucc 586] #[1496, 670],
  .addRup 1935 #[Int.ofNat 19038, Int.negSucc 587] #[1498, 672],
  .addRup 1936 #[Int.ofNat 19042, Int.negSucc 591] #[1506, 677],
  .addRup 1937 #[Int.ofNat 19043, Int.negSucc 592] #[1508, 678],
  .addRup 1938 #[Int.ofNat 19044, Int.negSucc 593] #[1510, 680],
  .addRup 1939 #[Int.negSucc 19036, Int.ofNat 19111] #[1494, 726],
  .addRup 1940 #[Int.ofNat 19113, Int.negSucc 19037, Int.negSucc 19110] #[1494, 727],
  .addRup 1941 #[Int.negSucc 19112, Int.ofNat 19114] #[1494, 728],
  .addRup 1942 #[Int.negSucc 19113, Int.ofNat 19116] #[1494, 729],
  .addRup 1943 #[Int.negSucc 19115, Int.ofNat 19118] #[1494, 730],
  .addRup 1944 #[Int.negSucc 19117, Int.ofNat 19120] #[1494, 731],
  .addRup 1945 #[Int.negSucc 19041, Int.negSucc 19117] #[1494, 732],
  .addRup 1946 #[Int.negSucc 19119, Int.ofNat 19122] #[1494, 733],
  .addRup 1947 #[Int.negSucc 19042, Int.negSucc 19119] #[1494, 734],
  .addRup 1948 #[Int.negSucc 19043, Int.negSucc 19121] #[1494, 735],
  .addRup 1949 #[Int.ofNat 19477, Int.ofNat 587] #[1494, 1495, 736, 741],
  .addRup 1950 #[Int.ofNat 19624, Int.ofNat 588] #[1494, 1497, 749, 754],
  .addRup 1951 #[Int.ofNat 19771, Int.ofNat 589] #[1494, 1499, 762, 769],
  .addRup 1952 #[Int.ofNat 19918, Int.ofNat 590] #[1494, 1501, 777, 784],
  .addRup 1953 #[Int.ofNat 20065, Int.ofNat 591] #[1494, 1503, 792, 796],
  .addRup 1954 #[Int.ofNat 23177, Int.negSucc 864] #[1494, 803],
  .addRup 1955 #[Int.ofNat 23178, Int.negSucc 1142] #[1498, 805],
  .addRup 1956 #[Int.ofNat 23182, Int.negSucc 1146] #[1506, 809],
  .addRup 1957 #[Int.ofNat 23183, Int.negSucc 1147] #[1508, 810],
  .addRup 1958 #[Int.ofNat 23184, Int.negSucc 1148] #[1510, 812],
  .addRup 1959 #[Int.negSucc 23176, Int.ofNat 23251] #[1496, 858],
  .addRup 1960 #[Int.ofNat 23253, Int.negSucc 23177, Int.negSucc 23250] #[1496, 859],
  .addRup 1961 #[Int.negSucc 23252, Int.ofNat 23254] #[1496, 860],
  .addRup 1962 #[Int.negSucc 23253, Int.ofNat 23256] #[1496, 861],
  .addRup 1963 #[Int.negSucc 23255, Int.ofNat 23258] #[1496, 862],
  .addRup 1964 #[Int.negSucc 23257, Int.ofNat 23260] #[1496, 863],
  .addRup 1965 #[Int.negSucc 23181, Int.negSucc 23257] #[1496, 864],
  .addRup 1966 #[Int.negSucc 23259, Int.ofNat 23262] #[1496, 865],
  .addRup 1967 #[Int.negSucc 23182, Int.negSucc 23259] #[1496, 866],
  .addRup 1968 #[Int.negSucc 23183, Int.negSucc 23261] #[1496, 867],
  .addRup 1969 #[Int.ofNat 23446, Int.ofNat 865] #[1493, 1496, 868, 873],
  .addRup 1970 #[Int.ofNat 23764, Int.ofNat 1143] #[1496, 1497, 881, 886],
  .addRup 1971 #[Int.ofNat 23911, Int.ofNat 1144] #[1496, 1499, 894, 903],
  .addRup 1972 #[Int.ofNat 24058, Int.ofNat 1145] #[1496, 1501, 911, 917],
  .addRup 1973 #[Int.ofNat 24205, Int.ofNat 1146] #[1496, 1503, 925, 930],
  .addRup 1974 #[Int.ofNat 27317, Int.negSucc 865] #[1494, 937],
  .addRup 1975 #[Int.ofNat 27318, Int.negSucc 1419] #[1496, 939],
  .addRup 1976 #[Int.ofNat 27322, Int.negSucc 1699] #[1506, 944],
  .addRup 1977 #[Int.ofNat 27323, Int.negSucc 1700] #[1508, 945],
  .addRup 1978 #[Int.ofNat 27324, Int.negSucc 1701] #[1510, 947],
  .addRup 1979 #[Int.negSucc 27316, Int.ofNat 27391] #[1498, 993],
  .addRup 1980 #[Int.ofNat 27393, Int.negSucc 27317, Int.negSucc 27390] #[1498, 994],
  .addRup 1981 #[Int.negSucc 27392, Int.ofNat 27394] #[1498, 995],
  .addRup 1982 #[Int.negSucc 27393, Int.ofNat 27396] #[1498, 996],
  .addRup 1983 #[Int.negSucc 27395, Int.ofNat 27398] #[1498, 997],
  .addRup 1984 #[Int.negSucc 27397, Int.ofNat 27400] #[1498, 998],
  .addRup 1985 #[Int.negSucc 27321, Int.negSucc 27397] #[1498, 999],
  .addRup 1986 #[Int.negSucc 27399, Int.ofNat 27402] #[1498, 1000],
  .addRup 1987 #[Int.negSucc 27322, Int.negSucc 27399] #[1498, 1001],
  .addRup 1988 #[Int.negSucc 27323, Int.negSucc 27401] #[1498, 1002],
  .addRup 1989 #[Int.ofNat 27586, Int.ofNat 866] #[1493, 1498, 1003, 1008],
  .addRup 1990 #[Int.ofNat 27733, Int.ofNat 1420] #[1495, 1498, 1016, 1025],
  .addRup 1991 #[Int.ofNat 28051, Int.ofNat 1697] #[1498, 1499, 1033, 1038],
  .addRup 1992 #[Int.ofNat 28198, Int.ofNat 1698] #[1498, 1501, 1046, 1051],
  .addRup 1993 #[Int.ofNat 28345, Int.ofNat 1699] #[1498, 1503, 1059, 1064],
  .addRup 1994 #[Int.ofNat 31457, Int.negSucc 866] #[1494, 1073],
  .addRup 1995 #[Int.ofNat 31458, Int.negSucc 1420] #[1496, 1075],
  .addRup 1996 #[Int.ofNat 31459, Int.negSucc 1972] #[1498, 1077],
  .addRup 1997 #[Int.ofNat 31462, Int.negSucc 2250] #[1506, 1081],
  .addRup 1998 #[Int.ofNat 31463, Int.negSucc 2251] #[1508, 1083],
  .addRup 1999 #[Int.ofNat 31464, Int.negSucc 2252] #[1510, 1085],
  .addRup 2000 #[Int.ofNat 31462, Int.ofNat 31457, Int.ofNat 31458, Int.ofNat 31459, Int.ofNat 31463, Int.ofNat 31464] #[1500, 1502, 1504, 1512, 1514, 1516, 1518, 1520, 1522, 1524, 1526, 1528, 1530, 1532, 1534, 1536, 1538, 1540, 1542, 1544, 1546, 1078, 1079, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103, 1104],
  .addRup 2001 #[Int.negSucc 31456, Int.ofNat 31579] #[1500, 1105],
  .addRup 2002 #[Int.negSucc 31578, Int.ofNat 31580] #[1500, 1106],
  .addRup 2003 #[Int.negSucc 31457, Int.negSucc 31578] #[1500, 1107],
  .addRup 2004 #[Int.negSucc 31457, Int.ofNat 31580] #[1500, 1108],
  .addRup 2005 #[Int.negSucc 31579, Int.ofNat 31581] #[1500, 1109],
  .addRup 2006 #[Int.negSucc 31458, Int.negSucc 31579] #[1500, 1110],
  .addRup 2007 #[Int.negSucc 31580, Int.ofNat 31582] #[1500, 1111],
  .addRup 2008 #[Int.negSucc 31581, Int.ofNat 31583] #[1500, 1112],
  .addRup 2009 #[Int.negSucc 31582, Int.ofNat 31584] #[1500, 1113],
  .addRup 2010 #[Int.negSucc 31461, Int.negSucc 31582] #[1500, 1114],
  .addRup 2011 #[Int.negSucc 31461, Int.ofNat 31584] #[1500, 1115],
  .addRup 2012 #[Int.negSucc 31583, Int.ofNat 31585] #[1500, 1116],
  .addRup 2013 #[Int.negSucc 31462, Int.negSucc 31583] #[1500, 1117],
  .addRup 2014 #[Int.negSucc 31462, Int.ofNat 31585] #[1500, 1118],
  .addRup 2015 #[Int.negSucc 31463, Int.negSucc 31584] #[1500, 1119],
  .addRup 2016 #[Int.ofNat 31922, Int.ofNat 1973, Int.ofNat 31899, Int.ofNat 31900, Int.ofNat 31901, Int.ofNat 31902, Int.ofNat 31903, Int.ofNat 31904, Int.ofNat 31905, Int.ofNat 31906, Int.ofNat 31907, Int.ofNat 31908, Int.ofNat 31909, Int.ofNat 31910, Int.ofNat 31911, Int.ofNat 31912, Int.ofNat 31913, Int.ofNat 31914, Int.ofNat 31915, Int.ofNat 31916, Int.ofNat 31917, Int.ofNat 31918, Int.ofNat 31919, Int.ofNat 31920, Int.ofNat 31921, Int.ofNat 31923] #[1500, 1135, 1145],
  .addRup 2017 #[Int.ofNat 35597, Int.negSucc 867] #[1494, 1211],
  .addRup 2018 #[Int.ofNat 35598, Int.negSucc 1421] #[1496, 1213],
  .addRup 2019 #[Int.ofNat 35599, Int.negSucc 1973] #[1498, 1215],
  .addRup 2020 #[Int.ofNat 35602, Int.negSucc 2799] #[1506, 1219],
  .addRup 2021 #[Int.ofNat 35603, Int.negSucc 2800] #[1508, 1221],
  .addRup 2022 #[Int.ofNat 35603, Int.ofNat 35597, Int.ofNat 35598, Int.ofNat 35599, Int.ofNat 35602, Int.ofNat 35604] #[1500, 1502, 1504, 1512, 1514, 1516, 1518, 1520, 1522, 1524, 1526, 1528, 1530, 1532, 1534, 1536, 1538, 1540, 1542, 1544, 1546, 1216, 1217, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231, 1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241],
  .addRup 2023 #[Int.negSucc 35596, Int.ofNat 35719] #[1502, 1242],
  .addRup 2024 #[Int.negSucc 35718, Int.ofNat 35720] #[1502, 1243],
  .addRup 2025 #[Int.negSucc 35597, Int.negSucc 35718] #[1502, 1244],
  .addRup 2026 #[Int.negSucc 35597, Int.ofNat 35720] #[1502, 1245],
  .addRup 2027 #[Int.negSucc 35598, Int.negSucc 35719] #[1502, 1246],
  .addRup 2028 #[Int.negSucc 35601, Int.ofNat 35724] #[1502, 1247],
  .addRup 2029 #[Int.negSucc 35602, Int.negSucc 35723] #[1502, 1248],
  .addRup 2030 #[Int.ofNat 39737, Int.negSucc 868] #[1494, 1298],
  .addRup 2031 #[Int.ofNat 39738, Int.negSucc 1422] #[1496, 1300],
  .addRup 2032 #[Int.ofNat 39739, Int.negSucc 1974] #[1498, 1302],
  .addRup 2033 #[Int.ofNat 39742, Int.negSucc 3346] #[1506, 1306],
  .addRup 2034 #[Int.ofNat 39743, Int.negSucc 3347] #[1508, 1308],
  .addRup 2035 #[Int.ofNat 39744, Int.negSucc 3348] #[1510, 1310],
  .addRup 2036 #[Int.ofNat 39742, Int.ofNat 39737, Int.ofNat 39738, Int.ofNat 39739, Int.ofNat 39743, Int.ofNat 39744] #[1500, 1502, 1504, 1512, 1514, 1516, 1518, 1520, 1522, 1524, 1526, 1528, 1530, 1532, 1534, 1536, 1538, 1540, 1542, 1544, 1546, 1303, 1304, 1311, 1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327, 1328, 1329],
  .addRup 2037 #[Int.negSucc 39736, Int.ofNat 39859] #[1504, 1330],
  .addRup 2038 #[Int.negSucc 39858, Int.ofNat 39860] #[1504, 1331],
  .addRup 2039 #[Int.negSucc 39737, Int.negSucc 39858] #[1504, 1332],
  .addRup 2040 #[Int.negSucc 39737, Int.ofNat 39860] #[1504, 1333],
  .addRup 2041 #[Int.negSucc 39738, Int.negSucc 39859] #[1504, 1334],
  .addRup 2042 #[Int.negSucc 39741, Int.ofNat 39864] #[1504, 1335],
  .addRup 2043 #[Int.negSucc 39863, Int.ofNat 39865] #[1504, 1336],
  .addRup 2044 #[Int.negSucc 39742, Int.negSucc 39863] #[1504, 1337],
  .addRup 2045 #[Int.negSucc 39742, Int.ofNat 39865] #[1504, 1338],
  .addRup 2046 #[Int.negSucc 39743, Int.negSucc 39864] #[1504, 1339],
  .addRup 2047 #[Int.negSucc 48045, Int.ofNat 48048] #[1500, 1508, 1395, 1425],
  .addRup 2048 #[Int.negSucc 48047, Int.ofNat 48050] #[1502, 1508, 1396, 1426],
  .addRup 2049 #[Int.negSucc 48049, Int.ofNat 48052] #[1504, 1508, 1397, 1427],
  .addRup 2050 #[Int.negSucc 48051, Int.ofNat 48023, Int.ofNat 48054] #[1508, 1428],
  .addRup 2051 #[Int.ofNat 48024, Int.negSucc 48053] #[1508, 1512, 1514, 1516, 1518, 1520, 1522, 1524, 1526, 1528, 1530, 1532, 1534, 1536, 1538, 1540, 1542, 1544, 1546, 1401, 1402, 1403, 1404, 1405, 1406, 1407, 1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1447, 1446, 1445, 1444, 1443, 1442, 1441, 1440, 1439, 1438, 1437, 1436, 1435, 1434, 1433, 1432, 1431, 1430, 1429],
  .addRup 2052 #[Int.ofNat 1144, Int.negSucc 1145, Int.ofNat 15511, Int.negSucc 15534] #[364, 1971, 1854, 904, 1856, 906, 1857, 908, 1862, 910, 369, 902],
  .addRup 2053 #[Int.negSucc 15657, Int.negSucc 587, Int.negSucc 1142] #[431, 779, 914, 1713, 1882, 1867, 1881, 1880, 1866, 1952, 788, 785],
  .addRup 2054 #[Int.negSucc 587, Int.negSucc 1142, Int.negSucc 1143, Int.negSucc 1145, Int.ofNat 15096, Int.ofNat 15216, Int.negSucc 15243, Int.ofNat 27612, Int.ofNat 27614, Int.ofNat 27615] #[2053, 1767, 1868, 68, 1992, 66, 1053, 64, 62, 60, 58, 56, 54, 53, 52, 51, 50, 1768, 1869, 427, 1047, 138, 1779, 1777, 136, 1771, 1723, 47, 49, 48],
  .addRup 2055 #[Int.ofNat 591, Int.ofNat 1697, Int.ofNat 1699, Int.ofNat 15831] #[492, 1953, 366, 496, 1022, 1993, 1887, 798, 1065, 1888, 1889, 1068, 1895, 494, 1061, 793, 213, 1990, 211, 1949, 1026, 1799, 742, 1028, 1801, 744, 745, 1031, 1802, 747, 1725, 1018, 1763, 294, 1836, 1765, 1656, 1955, 1769, 1803, 215, 1995, 1140, 738, 2003, 2004, 362, 2001, 2006, 1852, 1994, 1996, 2052, 140, 290, 1148, 1657, 1781, 1150, 2054, 286, 1950, 1826, 755, 1827, 757, 1834, 760, 1835, 292, 2019, 1142, 752, 2027, 433, 427, 2024, 2026, 1869, 2023, 2018, 2017, 217, 142, 1808, 1809, 219, 2031, 2039, 2037, 2030, 144, 1787, 1786, 1785, 1778, 1777, 136, 1771, 1655, 1954, 47, 1959, 48, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967, 1956, 1968, 1957, 1660, 1958, 1661, 1662, 1363, 1368, 1369, 1372, 1365, 434, 1879, 1878, 1872, 1871, 429, 1658, 49, 50, 51, 52, 53, 54, 56, 58, 60, 62, 64, 66, 68, 70, 71, 72, 1671, 74, 75, 76, 1673, 78, 1721, 80, 1677, 83],
  .addRup 2056 #[Int.negSucc 15242, Int.ofNat 588, Int.negSucc 590, Int.negSucc 1145, Int.ofNat 1420, Int.ofNat 1697, Int.negSucc 15094, Int.ofNat 27612, Int.ofNat 27615] #[1802, 1710, 286, 1950, 1826, 755, 1827, 757, 759, 761, 753, 294, 1836, 1765, 750, 1949, 742, 744, 746, 748, 740, 219, 1809, 1804, 1808, 1803, 217, 215, 2018, 1995, 2026, 2004, 2027, 2006, 2019, 1996, 292, 290, 1835, 1834],
  .addRup 2057 #[Int.ofNat 588, Int.negSucc 590, Int.negSucc 1143, Int.negSucc 1145, Int.ofNat 1697, Int.negSucc 15094, Int.ofNat 27612, Int.ofNat 27615] #[1710, 286, 1950, 1991, 1826, 755, 1039, 757, 1042, 759, 1035, 761, 213, 753, 294, 1836, 1831, 2056, 1801, 1799, 211, 750, 288, 1970, 1828, 887, 1830, 890, 290, 883],
  .addRup 2058 #[Int.ofNat 1143, Int.negSucc 587, Int.negSucc 1143, Int.negSucc 1145, Int.ofNat 15069, Int.negSucc 15241, Int.ofNat 15393] #[1733, 882, 136, 1969, 1777, 874, 1779, 876, 877, 878, 870, 880, 140, 872, 1781, 144, 1782, 1787],
  .addRup 2059 #[Int.ofNat 865, Int.negSucc 23325] #[1969, 874, 877],
  .addRup 2060 #[Int.negSucc 15243, Int.negSucc 587, Int.negSucc 1142, Int.negSucc 1143, Int.negSucc 1145, Int.ofNat 15216, Int.ofNat 27612, Int.ofNat 27614, Int.ofNat 27615] #[1725, 2053, 1767, 68, 66, 64, 62, 60, 58, 56, 54, 53, 52, 51, 50, 2054, 1781, 140, 870, 2059, 1771, 1723, 47, 49, 48],
  .addRup 2061 #[Int.negSucc 864, Int.negSucc 1142, Int.negSucc 1143, Int.negSucc 1145, Int.ofNat 15393, Int.ofNat 15658] #[1771, 1655, 1954, 1723, 1657, 1656, 1955, 47, 1959, 1658, 48, 1960, 49, 1961, 50, 1962, 51, 1963, 52, 1964, 1965, 53, 1966, 1967, 1956, 54, 1968, 1957, 1660, 56, 1958, 1661, 58, 1662, 60, 62, 64, 66, 68, 70, 71, 72, 1671, 74, 75, 76, 1673, 78, 1721, 80, 1677, 83],
  .addRup 2062 #[Int.negSucc 1145, Int.negSucc 590, Int.negSucc 1143, Int.ofNat 1697, Int.ofNat 15069, Int.ofNat 27612, Int.ofNat 27615] #[1991, 1784, 1039, 1042, 1035, 213, 1990, 1806, 1026, 1028, 2057, 1718, 294, 1836, 1031, 2058, 2053, 2060, 1807, 215, 1995, 2003, 2001, 1994, 140, 2061, 136, 1969, 1777, 874, 1779, 876, 1781, 878, 1782, 880, 1787, 872, 144],
  .addRup 2063 #[Int.negSucc 1143, Int.negSucc 590, Int.ofNat 1697, Int.ofNat 1699] #[1632, 1993, 366, 1991, 1066, 1060, 138, 1989, 1009, 1011, 1014, 1022, 1039, 1017, 1042, 2062, 1973, 932, 926, 2059, 136, 1969, 870, 1777, 874, 140, 1779, 876, 1781, 879, 1782, 1783, 1725, 1787, 142, 1802, 144, 2017, 1006, 871, 2030, 2023, 431, 2037, 2024, 2025, 1719, 2038, 2039, 2027, 2018, 1869, 2041, 2031, 2019, 427, 2032, 292, 1631, 294, 1836, 1835, 1035, 213, 1806, 1801, 1807, 1799, 215, 211, 1995, 1770, 1628, 1934, 1260, 1351, 2004, 1939, 1264, 1355, 2006, 1265, 1356, 1996, 1268, 1359, 290, 1262, 1353, 1834, 368, 369, 1827, 1862, 1826, 1861, 286, 1860, 1629, 1935, 3, 1853, 1940, 1852, 1941, 362, 1942, 1630, 4, 1943, 5, 1944, 1945, 6, 1946, 1947, 1936, 7, 1948, 1937, 1633, 8, 1938, 1634, 9, 1635, 10, 11, 12, 13, 1636, 14, 15, 1637, 16, 17, 1638, 18, 19, 1639, 20, 21, 1640, 22, 23, 1641, 24, 25, 1642, 26, 27, 1643, 28, 29, 1644, 30, 31, 1645, 32, 33, 1646, 34, 35, 1647, 36, 37, 1648, 38, 39, 1649, 40, 41, 1650, 42, 43, 1651, 44, 1652, 1653, 1654],
  .addRup 2064 #[Int.negSucc 586, Int.negSucc 867, Int.negSucc 868, Int.negSucc 1420, Int.negSucc 15537] #[1260, 1351, 2030, 2017, 2037, 2023, 2039, 2025, 2031, 2018, 1355, 1264, 1356, 1265, 1359, 1268, 1353, 1262, 369, 368, 1862, 1861],
  .addRup 2065 #[Int.negSucc 15097, Int.negSucc 587, Int.negSucc 15241, Int.negSucc 15537] #[1782, 1783, 1725, 1787, 142, 1802, 1807, 144, 215, 2064, 211, 1949, 1799, 743, 1801, 737, 213],
  .addRup 2066 #[Int.ofNat 587, Int.negSucc 587, Int.ofNat 15243] #[211, 1949, 1799, 1801, 213, 743, 737],
  .addRup 2067 #[Int.negSucc 868, Int.negSucc 587, Int.negSucc 590, Int.negSucc 866, Int.negSucc 15243, Int.ofNat 15510, Int.ofNat 15511, Int.ofNat 15658, Int.ofNat 23792] #[2030, 1994, 1632, 1629, 1935, 2037, 2001, 2039, 2003, 2031, 1995, 219, 215, 1809, 1804, 1808, 1803, 217, 2066, 1770, 1628, 1934, 1124, 3, 1939, 1128, 1940, 1129, 1941, 1132, 1942, 1126, 1943, 433, 1944, 1945, 1946, 1947, 1936, 1948, 1937, 1633, 1938, 1634, 1635, 1351, 1355, 1356, 1358, 1361, 1354, 434, 1879, 1878, 1877, 1870, 1876, 1869, 429, 427, 900, 1631, 368, 1858, 1856, 1854, 1852, 362, 1630, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 1636, 14, 15, 1637, 16, 17, 1638, 18, 19, 1639, 20, 21, 1640, 22, 23, 1641, 24, 25, 1642, 26, 27, 1643, 28, 29, 1644, 30, 31, 1645, 32, 33, 1646, 34, 35, 1647, 36, 37, 1648, 38, 39, 1649, 40, 41, 1650, 42, 43, 1651, 44, 1652, 1653, 1654],
  .addRup 2068 #[Int.negSucc 15241, Int.negSucc 587, Int.negSucc 590, Int.negSucc 15095, Int.ofNat 15510, Int.ofNat 15511, Int.ofNat 15658, Int.negSucc 15831, Int.ofNat 23792] #[1780, 1859, 1860, 2065, 1781, 140, 1994, 2001, 2003, 1995, 215, 1807, 2067, 144, 1787, 1786, 142, 2017, 2023, 2025, 2018, 217, 1805, 1808, 1803, 1809, 2066, 219, 1124, 1128, 1129, 1131, 1134, 1127, 498, 1896, 1897, 500, 1263, 1270, 1267, 1260, 1265, 1264],
  .addRup 2069 #[Int.negSucc 588, Int.negSucc 589, Int.negSucc 590, Int.negSucc 742, Int.ofNat 130817, Int.ofNat 130818, Int.ofNat 130822, Int.ofNat 130823, Int.ofNat 130824] #[1630, 4, 1631, 1632, 5, 6, 7, 8, 9, 10, 11, 12, 13, 1636, 14, 15, 1637, 16, 17, 1638, 18, 19, 1639, 20, 21, 1640, 22, 23, 1641, 24, 25, 1642, 26, 27, 1643, 28, 29, 1644, 30, 31, 1645, 32, 33, 1646, 34, 35, 1647, 36, 37, 1648, 38, 39, 1649, 40, 41, 1650, 42, 43, 1651, 44, 1652, 1653, 1654],
  .addRup 2070 #[Int.negSucc 589, Int.negSucc 590, Int.negSucc 742, Int.ofNat 15510, Int.ofNat 15511, Int.ofNat 130817, Int.ofNat 130818, Int.ofNat 130822, Int.ofNat 130823, Int.ofNat 130824] #[2069, 362, 1951, 1852, 770, 1854, 772, 1856, 775, 1858, 767, 368],
  .addRup 2071 #[Int.ofNat 15658, Int.negSucc 587, Int.negSucc 590, Int.negSucc 15095, Int.ofNat 15510, Int.ofNat 15511, Int.negSucc 15831, Int.ofNat 23792] #[1868, 1629, 1935, 1992, 1052, 1055, 2068, 1800, 1806, 1799, 213, 211, 1048, 1770, 1628, 1934, 429, 3, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1936, 1948, 1937, 1633, 1938, 1634, 1635, 2070, 427, 1952, 1869, 785, 1871, 787, 1873, 789, 1874, 791, 1879, 783, 434],
  .addRup 2072 #[Int.negSucc 587, Int.negSucc 590, Int.ofNat 1697, Int.negSucc 15095, Int.ofNat 15510, Int.negSucc 15831, Int.ofNat 23792, Int.ofNat 27467] #[1629, 1935, 366, 1780, 2071, 431, 779, 1746, 1854, 1852, 362, 1006, 142, 1783, 1786, 1781, 1787, 140, 144, 1994, 2030, 2001, 2037, 2003, 2039, 1995, 2031, 215, 219, 1809, 1804, 1803, 2066, 1770, 1628, 1934, 3, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1936, 1948, 1937, 1633, 1938, 1634, 1635, 2069, 1952, 788, 785],
  .addRup 2073 #[Int.negSucc 15389, Int.ofNat 588, Int.ofNat 1699, Int.ofNat 15831, Int.ofNat 23791] #[1950, 1761, 755, 2055, 366, 757, 758, 2063, 759, 364, 761, 753, 294, 1836, 1831, 1830, 290, 751, 362, 1951, 1852, 770, 1854, 772, 1856, 774, 1857, 776, 1862, 768, 369],
  .addRup 2074 #[Int.negSucc 15390, Int.negSucc 15095, Int.negSucc 15241, Int.ofNat 15246, Int.ofNat 15393] #[1835, 292, 2019, 2027, 2024, 2026, 2023, 2018, 2017, 217, 142, 1808, 1783, 1807, 1781, 215, 140, 1995, 1994, 2003, 2001],
  .addRup 2075 #[Int.ofNat 588, Int.ofNat 1699, Int.negSucc 15095, Int.ofNat 15831, Int.ofNat 23791] #[1710, 286, 1950, 1761, 1826, 755, 2055, 1827, 757, 759, 761, 753, 294, 1836, 2073, 1828, 288, 750, 211, 1949, 1799, 742, 1800, 744, 746, 748, 740, 219, 1809, 2074, 1834, 290, 1996, 2006, 2002, 2004, 2001, 1995, 1994, 215, 140, 1807, 1781, 1725],
  .addRup 2076 #[Int.ofNat 865, Int.ofNat 1699, Int.ofNat 15831, Int.ofNat 23791] #[136, 1969, 496, 1993, 1761, 1777, 874, 1065, 1066, 2055, 366, 876, 1068, 2063, 1060, 364, 1971, 138, 1989, 1859, 904, 1779, 1009, 1860, 906, 1780, 1011, 909, 878, 2075, 1629, 1935, 908, 1014, 880, 910, 2072, 1895, 1894, 494, 2052, 1061, 1852, 213, 362, 1806, 902, 369, 1862, 1861, 368, 900, 429, 872, 144, 1787, 1782, 1786, 1781, 142, 140, 2017, 1994, 2023, 2001, 2024, 2025, 2002, 2003, 2027, 2018, 2006, 1995, 2019, 217, 1996, 215, 292, 1805, 290, 1807, 1803, 1808, 2066, 1809, 1770, 1628, 1934, 219, 3, 1939, 2031, 1940, 2040, 1941, 2041, 1942, 2032, 1943, 294, 1944, 1945, 1836, 1946, 1947, 1936, 1835, 1948, 1937, 1633, 1834, 1938, 1634, 1833, 1635, 288, 2069, 2053, 427, 1952, 1869, 785, 1871, 787, 1873, 790, 1875, 780, 433],
  .addRup 2077 #[Int.ofNat 23791, Int.ofNat 1699, Int.ofNat 15831] #[2076, 1761, 366, 2055, 926, 2063, 1971, 905, 895, 362, 1852, 2052, 1973, 932],
  .addRup 2078 #[Int.ofNat 1420, Int.ofNat 15245, Int.negSucc 23790] #[213, 1990, 897, 1714, 1026, 1851, 1850, 1865, 1864, 1863, 1849, 1951, 771, 763, 211, 1799, 1801, 1803, 215, 1029, 1020],
  .addRup 2079 #[Int.negSucc 590, Int.ofNat 1699, Int.negSucc 23790] #[897, 1714, 1993, 1851, 1850, 1865, 1864, 1863, 1849, 1951, 770, 771, 773, 763, 766, 211, 1949, 286, 1950, 1799, 742, 1826, 755, 1800, 744, 1827, 757, 759, 761, 753, 294, 1836, 1066, 746, 1060, 138, 1989, 1010, 748, 740, 219, 1809, 1804, 2078, 1004, 2059, 136, 870, 1777, 140, 1779, 1781, 1783, 1725, 142, 1807, 2017, 215, 2023, 1995, 2024, 2004, 2027, 2006, 2019, 1996, 292, 290, 1835, 1834],
  .addRup 2080 #[Int.negSucc 23790, Int.ofNat 1699] #[896, 1714, 496, 1993, 1656, 1955, 1657, 1850, 1065, 1067, 1070, 897, 1062, 1851, 498, 1865, 1864, 1863, 1849, 1951, 770, 771, 773, 763, 766, 1949, 286, 742, 1826, 744, 1827, 747, 2079, 492, 1887, 1720, 1068, 1069, 1888, 1061, 1071, 1895, 1896, 1897, 500, 2078, 1804, 1805, 1809, 217, 219, 2018, 739, 2031, 2025, 2026, 427, 2039, 2040, 2023, 2027, 1869, 2037, 2041, 2017, 2019, 2030, 2032, 142, 292, 144, 294, 1787, 1836, 1786, 1835, 1834, 290, 1996, 2006, 2002, 2001, 1994, 140, 1785, 1778, 1777, 136, 1771, 1655, 1954, 47, 1959, 48, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967, 1956, 1968, 1957, 1660, 1958, 1661, 1662, 1063, 431, 1719, 1658, 49, 50, 51, 52, 53, 54, 56, 58, 60, 62, 64, 66, 68, 70, 71, 72, 1671, 74, 75, 76, 1673, 78, 1721, 80, 1677, 83],
  .addRup 2081 #[Int.ofNat 865, Int.negSucc 865, Int.ofNat 1975, Int.negSucc 2524, Int.ofNat 15071, Int.ofNat 15390, Int.ofNat 15391] #[136, 1969, 1777, 875, 1778, 869, 288, 1833, 1828, 1834, 1826, 290, 286, 1996, 1364, 2006, 1370, 2002, 1367, 2001, 1366, 1994, 1362, 140, 144, 1785, 1787, 1786],
  .addRup 2082 #[Int.ofNat 1143, Int.negSucc 864, Int.ofNat 15390] #[288, 1828, 1826, 286, 1733, 882],
  .addRup 2083 #[Int.ofNat 1421, Int.negSucc 2249, Int.negSucc 15242, Int.negSucc 31753] #[215, 1803, 1804, 1809, 219, 1127, 1134, 1133],
  .addRup 2084 #[Int.negSucc 15242, Int.ofNat 1699] #[2080, 496, 2077, 1993, 1891, 1065, 1892, 1893, 1067, 1897, 498, 1070, 500, 1909, 1062, 1908, 366, 1903, 1902, 1899, 1884, 1898, 1887, 1883, 1720, 1953, 364, 1971, 797, 904, 799, 906, 801, 909, 795, 362, 1951, 1852, 770, 1854, 772, 1856, 1746, 775, 1857, 1858, 431, 1862, 368, 369, 767, 427, 1869, 1748, 1797, 900, 429, 1871, 1873, 1874, 1875, 1879, 433, 434, 1126, 1354, 2083, 1796, 1353, 1818, 1819, 1820, 1798, 1361, 1360],
  .addRup 2085 #[Int.negSucc 866, Int.ofNat 1699, Int.ofNat 15216] #[1994, 2084, 2080, 496, 2077, 1993, 1806, 2001, 1801, 1891, 1065, 2003, 1799, 1892, 1893, 1067, 1995, 211, 1897, 498, 1070, 215, 1909, 1062, 1807, 1908, 366, 1903, 1902, 1899, 1884, 1898, 1887, 1883, 1720, 1953, 364, 797, 799, 801, 795, 362, 1951, 1852, 770, 1854, 772, 1856, 1746, 775, 1858, 431, 368, 767, 427, 1952, 1869, 786, 778, 429, 1871, 1873, 1875, 433, 1124, 1128, 1129, 1131, 1132, 1134, 1126, 1127, 217, 219, 1808, 1809],
  .addRup 2086 #[Int.ofNat 15216, Int.ofNat 1699] #[2084, 2080, 496, 2077, 1993, 1749, 1801, 1891, 1065, 138, 1799, 1892, 1893, 1067, 211, 1897, 498, 1070, 1909, 1062, 1908, 366, 1903, 1902, 1899, 1884, 1898, 1887, 1883, 1720, 1953, 364, 797, 799, 801, 795, 362, 1951, 1852, 770, 1854, 772, 773, 1856, 1746, 774, 775, 1858, 431, 776, 368, 767, 427, 1952, 1869, 786, 778, 429, 1871, 1873, 1875, 433, 2085, 140, 901, 1742, 136, 1777, 1779, 1781, 1782, 1783, 1787, 142, 144, 1120, 1121, 1122, 1123],
  .addRup 2087 #[Int.negSucc 1420, Int.ofNat 1699] #[1796, 1995, 2086, 2084, 2080, 496, 2077, 1993, 1813, 2004, 1814, 213, 1891, 1065, 1811, 2006, 1892, 1893, 1067, 1810, 1996, 1897, 498, 1070, 1795, 290, 1909, 1062, 1949, 2066, 1908, 366, 742, 286, 1903, 745, 1826, 1902, 1899, 738, 1827, 1884, 1898, 362, 1834, 1887, 1852, 1720, 364, 1854, 1856, 1857, 1858, 1862, 368, 369, 1262, 1353, 1815, 1816, 1817, 1820, 1797, 1798, 1268, 1359, 1266, 1357, 1261, 1352, 292, 294, 1835, 1836],
  .addRup 2088 #[Int.ofNat 1423, Int.ofNat 587, Int.ofNat 1699] #[219, 211, 1949, 2087, 2086, 2084, 2080, 496, 2077, 1993, 1809, 1799, 742, 215, 213, 2066, 1891, 1065, 1800, 744, 1807, 286, 1892, 1893, 1067, 747, 1808, 1826, 1897, 498, 1070, 217, 1827, 1909, 1062, 2018, 739, 1908, 2026, 427, 1903, 2027, 1869, 1902, 1899, 2019, 1884, 1898, 292, 1887, 1883, 1720, 1953, 364, 797, 799, 801, 795, 362, 1852, 1854, 1746, 431, 1992, 1052, 1055, 1048, 429, 1871, 1873, 1874, 1875, 1879, 433, 434, 1126, 1354, 1132, 1361, 1130, 1358, 1125, 1357, 290, 1352, 1834, 294, 1835, 1836],
  .addRup 2089 #[Int.ofNat 587, Int.ofNat 1699] #[2086, 2080, 496, 2077, 1993, 213, 1891, 1065, 1892, 1893, 1067, 1897, 498, 1070, 500, 1909, 1062, 1908, 366, 1903, 1902, 1899, 1884, 1898, 1887, 1720, 364, 1859, 1860, 2088, 2031, 1127, 1263, 2040, 2041, 2032, 294, 1836, 2087, 1134, 1131, 1130, 1125, 290, 2084, 2066, 286, 1826, 1827, 1717, 1834, 1270, 1835, 1267, 292, 1266, 1261],
  .addRup 2090 #[Int.ofNat 15069, Int.ofNat 1699, Int.ofNat 15096] #[1779, 2086, 1777, 213, 136, 1004, 1773, 1989, 1010],
  .addRup 2091 #[Int.ofNat 31463, Int.ofNat 1699, Int.ofNat 16097, Int.ofNat 16098, Int.ofNat 16099, Int.ofNat 31457, Int.ofNat 31459, Int.negSucc 39743, Int.negSucc 48051] #[1998, 2089, 2086, 2080, 496, 2077, 1993, 1309, 2046, 604, 1795, 1891, 1065, 1810, 1892, 1893, 1067, 1811, 1897, 498, 1070, 1813, 500, 1909, 1062, 1796, 1908, 366, 1074, 1903, 1902, 1899, 1884, 1898, 1887, 1883, 1720, 1953, 364, 797, 799, 801, 795, 362, 1852, 1854, 1856, 1858, 368, 1928, 1290, 2045, 2034, 608, 1921, 606, 1933, 2021, 1931, 1932, 2029, 1930, 1927, 2028, 1926, 1084, 2000, 1080, 1294, 1295, 1296, 1291, 1399, 2051, 2050, 1398, 1284, 2020, 1288, 1282, 1286, 1285],
  .addRup 2092 #[Int.negSucc 39743, Int.ofNat 1699, Int.ofNat 15950, Int.ofNat 15951, Int.ofNat 15952, Int.ofNat 16097, Int.ofNat 16098, Int.ofNat 16099, Int.ofNat 31457, Int.ofNat 31459, Int.negSucc 48051] #[2086, 2080, 496, 2077, 1993, 213, 1891, 1065, 1892, 1893, 1067, 1897, 498, 1070, 1909, 1062, 1908, 366, 1903, 1902, 1899, 1884, 1898, 1887, 1883, 1720, 1953, 364, 797, 799, 801, 795, 362, 1951, 1852, 770, 1854, 772, 1856, 1746, 775, 1858, 431, 1992, 368, 1052, 767, 1055, 427, 1048, 1869, 429, 1871, 1873, 1875, 433, 1309, 2046, 2091, 1082, 2013, 2014, 2011, 2015, 1997, 1999, 1203, 2043, 2042, 2033, 570, 1207, 1208, 1209, 1204, 1399, 2051, 2050, 1398, 1197, 1201, 574, 1199, 1913, 1198, 572, 1195],
  .addRup 2093 #[Int.negSucc 31462, Int.ofNat 1699, Int.ofNat 2251, Int.ofNat 16244, Int.ofNat 16245, Int.ofNat 16246, Int.ofNat 39737, Int.ofNat 39739, Int.ofNat 39744, Int.negSucc 48051] #[2013, 2089, 2086, 2080, 496, 2077, 1993, 2030, 2035, 2009, 1795, 1891, 1065, 144, 642, 2008, 1810, 1892, 1893, 1067, 1787, 2007, 1811, 1897, 498, 1070, 1782, 2005, 1812, 1909, 1062, 2002, 1816, 1817, 1908, 1991, 2001, 1820, 1805, 1903, 1040, 1994, 1798, 1902, 1899, 140, 1299, 1884, 1898, 1781, 1887, 2090, 1720, 138, 364, 1971, 1034, 904, 362, 906, 1852, 909, 1854, 1746, 431, 1743, 1875, 433, 1082, 2014, 2015, 1999, 638, 1929, 640, 1918, 1202, 1922, 1205, 1923, 1925, 1920, 1307, 2036, 1305, 1206, 1196, 1208, 1200, 1209, 1201, 1204, 1399, 2051, 2050, 1398, 1197],
  .addRup 2094 #[Int.negSucc 4436, Int.ofNat 16097, Int.ofNat 16098, Int.ofNat 16099, Int.ofNat 16100, Int.ofNat 36951, Int.ofNat 41091] #[1382, 608, 1921, 606, 1291],
  .addRup 2095 #[Int.ofNat 16102, Int.ofNat 1699, Int.negSucc 4164, Int.ofNat 16097, Int.ofNat 16098, Int.ofNat 16099, Int.ofNat 16100, Int.ofNat 39737, Int.ofNat 39739, Int.ofNat 39744] #[2089, 2086, 2080, 496, 2077, 1795, 1891, 1810, 1892, 1811, 1897, 1812, 500, 1816, 1820, 1798, 1299, 1920, 1307, 2036, 1305, 1912, 1917, 1921, 1283, 1916, 606, 1911, 1284, 1287, 1288],
  .addRup 2096 #[Int.ofNat 31462, Int.ofNat 1699, Int.ofNat 16097, Int.ofNat 16098, Int.ofNat 16099, Int.ofNat 16244, Int.ofNat 16245, Int.ofNat 16246, Int.ofNat 31457, Int.ofNat 31459, Int.ofNat 35597, Int.ofNat 35599, Int.ofNat 39737, Int.ofNat 39739, Int.ofNat 39744, Int.negSucc 48051] #[2035, 2089, 2086, 2080, 496, 2077, 1993, 1994, 1996, 2017, 2019, 2032, 1795, 1891, 1065, 140, 290, 142, 292, 294, 1810, 1893, 1067, 1783, 1836, 1811, 498, 1070, 1781, 1835, 1812, 1813, 1062, 2090, 1834, 1816, 1796, 366, 1991, 138, 1827, 1833, 1820, 1074, 1040, 1034, 1826, 288, 1809, 362, 1951, 286, 1804, 1852, 771, 2053, 763, 364, 1971, 1854, 904, 1856, 906, 1857, 1858, 909, 1862, 368, 1743, 369, 1874, 1879, 434, 1997, 1817, 2093, 2000, 1797, 1998, 1084, 1212, 604, 1380, 1289, 1383, 1384, 1387, 1388, 1385, 1381, 1222, 1292, 1293, 1295, 1296, 2094, 1399, 2051, 2050, 1398, 2095, 1925, 608, 1375, 1924, 2034, 1919, 2044, 1220, 2042, 2022, 2033, 1379, 1218, 1378, 1374],
  .addRup 2097 #[Int.ofNat 868, Int.ofNat 867, Int.ofNat 1699, Int.ofNat 1973, Int.ofNat 1975, Int.ofNat 15391, Int.ofNat 35599] #[142, 140, 1072, 2089, 2086, 2080, 496, 2077, 1993, 290, 1829, 1783, 1795, 1934, 213, 1891, 1065, 1834, 1781, 1810, 1939, 1975, 1892, 1893, 1067, 1827, 1833, 1811, 1897, 498, 1070, 1826, 288, 1909, 1062, 286, 1955, 1908, 366, 1935, 2053, 1903, 1940, 1868, 1902, 1899, 1941, 1992, 1884, 1898, 1942, 1052, 1887, 1883, 1943, 1055, 1720, 1953, 1944, 1945, 1048, 364, 797, 1946, 1947, 1936, 429, 799, 1948, 1937, 801, 1938, 795, 362, 1951, 1852, 770, 1854, 772, 1856, 775, 1857, 1858, 1862, 368, 369, 767, 427, 1869, 1871, 1873, 1874, 1879, 434, 1210, 1076, 1301, 2090, 138, 1974, 1727, 1979, 1788, 1980, 1981, 1982, 1983, 1984, 1985, 1986, 1987, 1976, 1988, 1977, 1978, 1812, 567, 1481, 601, 635, 2081, 1954, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967, 1956, 1968, 1957, 1958, 1790, 1794, 1776, 569, 1483, 603, 637, 1816, 1712, 568, 602, 636, 1297, 1820, 2047, 1798, 2048, 1299, 2049, 2092, 2035, 2096, 642, 1080, 2011, 2012, 2015, 1373, 1910, 1999, 1914, 638, 1915, 1929, 1917, 640, 1912, 1381, 1305, 1376, 1386, 2036, 1377, 1387, 1307, 1379, 1388, 1382, 1375, 1399, 1398, 2051, 2050],
  .addRup 2098 #[Int.ofNat 867, Int.ofNat 1699, Int.ofNat 1973, Int.ofNat 1975, Int.ofNat 15391, Int.ofNat 35599] #[140, 2086, 2080, 496, 2077, 1993, 290, 213, 1891, 1065, 1834, 1892, 1893, 1067, 1827, 1833, 1897, 498, 1070, 1826, 288, 1909, 1062, 286, 1908, 366, 2053, 1903, 1868, 1902, 1899, 1992, 1884, 1898, 1052, 1887, 1883, 1055, 1720, 1953, 1048, 364, 797, 429, 799, 801, 795, 362, 1951, 1852, 770, 1854, 772, 1856, 775, 1858, 368, 767, 427, 1869, 1871, 1873, 1875, 433, 2097, 1775, 1120, 1791, 1122, 1788, 1727, 138, 1989, 1010, 1004, 136, 1777, 1779, 1781, 1782, 1787, 144, 1123, 1121],
  .addRup 2099 #[Int.ofNat 869, Int.negSucc 3072, Int.negSucc 15096, Int.negSucc 39886] #[144, 1787, 1786, 142, 1343, 1350, 1349],
  .addRup 2100 #[Int.ofNat 1973, Int.ofNat 1699, Int.ofNat 1975, Int.ofNat 15391, Int.ofNat 35599] #[290, 2086, 2080, 496, 2077, 1834, 213, 1891, 1827, 1833, 1892, 1893, 1826, 288, 1897, 498, 286, 898, 500, 1909, 2053, 366, 1908, 1868, 1903, 1992, 1902, 1899, 1052, 1884, 1898, 1055, 1887, 1883, 1048, 1720, 1953, 429, 364, 797, 799, 801, 795, 362, 1951, 1852, 770, 1854, 772, 1856, 775, 1857, 1858, 1862, 368, 369, 767, 427, 1869, 1871, 1873, 1874, 1879, 434, 2098, 1251, 1342, 1774, 1789, 1727, 138, 1989, 1010, 1004, 136, 1777, 1779, 1780, 1792, 2099, 1252, 1776, 1794, 1793, 1775, 1259, 1258],
  .addRup 2101 #[Int.ofNat 588, Int.negSucc 586, Int.ofNat 15390] #[286, 1826, 1828, 288, 1710, 750],
  .addRup 2102 #[Int.ofNat 1974, Int.ofNat 1699, Int.ofNat 1975, Int.ofNat 15391] #[2089, 2080, 496, 2077, 1993, 1829, 1891, 1065, 2101, 1892, 1893, 1067, 1821, 1897, 498, 1070, 1837, 1909, 1062, 1908, 366, 1903, 1902, 1899, 1884, 1898, 1887, 1883, 1720, 1953, 364, 797, 799, 801, 795, 362, 1852, 1854, 1856, 1857, 1858, 1862, 368, 369, 1214, 2100, 1996, 1823, 1364, 2006, 1841, 2002, 1839, 2001, 1822, 1994, 2082, 140, 136, 1777, 1778, 1785, 1273, 1370, 1279, 1367, 1276, 1366, 1275, 1362, 144, 1787, 1786, 142, 1271],
  .addRup 2103 #[Int.ofNat 15391, Int.ofNat 1699, Int.ofNat 1975] #[1829, 2089, 2101, 1821, 1837, 1838, 2102, 1824, 1845, 1840, 1843, 1839, 1834, 1833],
  .addRup 2104 #[Int.ofNat 1975, Int.ofNat 1699] #[294, 2089, 2080, 496, 2077, 1993, 1836, 1891, 1065, 1831, 1892, 1893, 1067, 1897, 498, 1070, 500, 1909, 1062, 1908, 366, 1903, 1902, 1899, 1884, 1898, 1887, 1883, 1720, 1953, 364, 797, 799, 801, 795, 362, 1951, 1852, 770, 1854, 772, 1856, 1746, 1857, 1858, 431, 1992, 1862, 368, 1052, 369, 1055, 2103, 1835, 292, 2019, 2027, 2024, 2023, 2017, 142, 1783, 2086, 213, 1048, 429, 775, 767, 427, 1869, 1871, 1873, 1874, 1875, 1879, 433, 434, 1142, 1845, 1840, 1365, 1372, 1371, 1364, 290, 1830, 2101, 1821, 1837, 1839, 1822, 2082, 136, 1777, 1778, 1150, 1147, 1146, 1138, 140, 1785, 1781, 1786, 1779, 1787, 138, 144, 1250, 1252, 1255, 1259, 1256],
  .addRup 2105 #[Int.ofNat 15390, Int.ofNat 1143, Int.ofNat 1699] #[896, 288, 1970, 2082, 2104, 2089, 496, 2077, 1993, 1828, 887, 136, 2032, 1825, 2101, 1891, 1065, 1826, 889, 1777, 2041, 1848, 1892, 1893, 1067, 1837, 891, 1778, 2038, 2040, 1844, 1897, 498, 1070, 1838, 893, 2037, 2031, 1909, 1144, 1062, 885, 2030, 219, 1908, 144, 1809, 1903, 1787, 1804, 1899, 1782, 1898, 1887, 1883, 1720, 1953, 364, 1971, 797, 904, 799, 906, 801, 909, 795, 362, 1852, 1854, 1746, 431, 1843, 1823, 1153, 1149, 1147, 1146, 1138, 140, 1785, 1781, 1786, 1779, 142, 138, 1341, 1743, 1346, 1874, 1347, 1879, 1350, 434, 1343],
  .addRup 2106 #[Int.negSucc 1973, Int.ofNat 1699] #[1824, 2104, 2089, 2080, 496, 2077, 1993, 1825, 1891, 1065, 1848, 1892, 1893, 1067, 1847, 1897, 498, 1070, 1842, 1909, 1062, 1838, 1908, 1837, 1903, 1821, 1902, 1899, 1950, 1884, 1898, 755, 1887, 1883, 757, 1720, 1953, 760, 364, 797, 752, 799, 427, 1952, 801, 1869, 786, 795, 778, 362, 429, 1852, 1871, 1854, 1746, 431, 1873, 1875, 433, 1142, 1846, 1823, 1144, 1151, 1153],
  .addRup 2107 #[Int.ofNat 1699] #[2106, 2104, 2089, 2080, 496, 2077, 1993, 1825, 1848, 1891, 1892, 1893, 1897, 498, 500, 1909, 1908, 1065, 1844, 1903, 1902, 1899, 1884, 1898, 1887, 1883, 1953, 797, 1067, 1840, 1720, 364, 799, 1070, 801, 1062, 366, 795, 362, 1852, 1854, 1856, 1858, 368, 1747, 2105, 1822, 1839, 1837, 1821, 2101],
  .addRup 2108 #[Int.ofNat 15878, Int.ofNat 15390] #[2107, 1899, 1898, 1883, 1953, 797, 800, 794, 286, 1826, 1828, 288, 928, 1902, 1884, 1973, 934, 931],
  .addRup 2109 #[Int.negSucc 588, Int.negSucc 590, Int.negSucc 742, Int.negSucc 2248, Int.ofNat 130817, Int.ofNat 130818, Int.ofNat 130822, Int.ofNat 130823, Int.ofNat 130824] #[780, 2069, 790, 1952, 787, 785],
  .addRup 2110 #[Int.negSucc 2248, Int.negSucc 587, Int.negSucc 590, Int.negSucc 742, Int.negSucc 865, Int.ofNat 15245, Int.ofNat 15833, Int.ofNat 19800, Int.ofNat 23792, Int.ofNat 23939, Int.ofNat 23940, Int.ofNat 130817, Int.ofNat 130822, Int.ofNat 130823, Int.ofNat 130824] #[1629, 2109, 362, 1951, 1852, 770, 772, 773, 774, 766, 776, 366, 768, 369, 1862, 1857, 1856, 1854, 364, 915],
  .addRup 2111 #[Int.ofNat 15363, Int.ofNat 15364, Int.ofNat 15365, Int.ofNat 15390, Int.ofNat 31899] #[2107, 1885, 1833, 1822, 2108, 1828, 1834, 1970, 2082, 1904, 1826, 1835, 887, 136, 1969, 1905, 1906, 286, 1836, 889, 1777, 1909, 1893, 1629, 1935, 1138, 294, 891, 1778, 1897, 140, 2032, 893, 1785, 1896, 2041, 885, 1890, 2038, 2040, 494, 916, 2037, 2031, 1889, 2030, 219, 1887, 144, 1809, 492, 1787, 1804, 1782, 1786, 1781, 142, 1779, 2017, 138, 2023, 1341, 2025, 1346, 2018, 217, 1808, 1802, 2066, 1770, 1934, 1628, 3, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1936, 1948, 1937, 1633, 1938, 1634, 1635, 874, 1347, 876, 1350, 879, 1343, 434, 1879, 871, 429, 1972, 1876, 918, 920, 782, 899, 923, 2110, 433, 1878, 1872, 1877, 1871, 431, 1869, 427, 2069, 362, 1951, 1852, 770, 771, 773, 763, 766, 364, 1746, 1854],
  .addRup 2112 #[Int.negSucc 587, Int.negSucc 1142, Int.ofNat 15217, Int.ofNat 15659, Int.ofNat 31899] #[2107, 1138, 140, 2053, 1868, 1992, 1052, 1053, 1054, 1055, 1056, 1058, 1050, 434, 1879, 1878, 1877, 1870, 1869, 427, 1876, 429, 1047, 138, 1989, 1784, 1785, 1048, 213, 1806, 1807, 1009, 1990, 1011, 1026, 1013, 1028, 1015, 1030, 1007, 144, 1787, 1786, 142, 2017, 2023, 2025, 2018, 217, 1808, 1809, 219, 1032, 1024],
  .addRup 2113 #[Int.ofNat 866, Int.negSucc 1419, Int.ofNat 15096] #[138, 1779, 1777, 136, 1989, 1004, 1010],
  .addRup 2114 #[Int.ofNat 1144, Int.negSucc 1142, Int.negSucc 1145, Int.negSucc 15534] #[1714, 898, 366, 2052],
  .addRup 2115 #[Int.negSucc 1143, Int.negSucc 1144, Int.negSucc 1145, Int.negSucc 1297, Int.ofNat 130843, Int.ofNat 130844, Int.ofNat 130848, Int.ofNat 130849, Int.ofNat 130850] #[48, 1657, 49, 1658, 50, 51, 52, 53, 54, 56, 58, 60, 62, 64, 66, 68, 70, 71, 72, 1671, 74, 75, 76, 1673, 78, 1721, 80, 1677, 83],
  .addRup 2116 #[Int.ofNat 15659, Int.ofNat 15364, Int.ofNat 15365, Int.ofNat 15390, Int.ofNat 32022] #[2107, 1885, 1823, 2108, 1147, 1148, 1904, 1146, 1905, 1906, 2111, 1909, 288, 1897, 1656, 1955, 1140, 1896, 215, 1890, 2112, 286, 1950, 1826, 755, 1827, 757, 1834, 759, 1835, 761, 1836, 294, 753, 2032, 492, 1953, 2041, 1887, 798, 2038, 2040, 1889, 2037, 2031, 494, 2030, 219, 793, 144, 1809, 211, 1949, 1787, 1804, 1799, 742, 1803, 1800, 744, 1801, 1807, 747, 213, 1808, 1352, 217, 1357, 2018, 739, 2025, 427, 2023, 1869, 2017, 142, 1786, 1780, 2113, 1727, 1789, 1785, 1778, 1777, 136, 1771, 1954, 1655, 47, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967, 1956, 1968, 1957, 1660, 1958, 1661, 1662, 1358, 1361, 1354, 434, 1879, 1878, 1872, 1871, 429, 2115, 1971, 2114, 905, 1852, 895, 362],
  .addRup 2117 #[Int.negSucc 1145, Int.negSucc 1142, Int.negSucc 2248, Int.ofNat 15217, Int.ofNat 15364, Int.ofNat 15365] #[2107, 1885, 1901, 1884, 1656, 1955, 1900, 1898, 1883, 1953, 797, 798, 800, 793, 794, 211, 1949, 286, 1799, 742, 1826, 1800, 1827, 1807, 1834, 1835, 1836, 294, 2032, 2041, 2038, 2040, 2037, 2031, 2030, 219, 144, 1809, 1787, 1804, 1808, 1803, 217, 1801, 2018, 213, 2025, 2023, 2017, 142, 1786, 1780, 2113, 744, 1727, 747, 1789, 1785, 1778, 1777, 136, 1771, 1954, 1655, 47, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967, 1956, 1968, 1957, 1660, 1958, 1661, 1662, 739, 427, 1952, 1869, 785, 787, 790, 780, 362, 1852, 2114, 2115, 1719, 1713, 431, 914],
  .addRup 2118 #[Int.ofNat 32022, Int.ofNat 15364, Int.ofNat 15365, Int.ofNat 15390] #[2107, 1823, 1147, 1148, 2116, 433, 1146, 2111, 288, 928, 1140, 215, 2117, 934, 1973, 931],
  .addRup 2119 #[Int.ofNat 1146, Int.negSucc 24084] #[1973, 934, 931],
  .addRup 2120 #[Int.negSucc 864, Int.negSucc 1142, Int.negSucc 1143] #[2107, 928, 2119, 1771, 1954, 1655, 1656, 1955, 47, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967, 1956, 1968, 1957, 1660, 1958, 1661, 1662, 2115, 1713, 1723, 431, 914],
  .addRup 2121 #[Int.negSucc 1142, Int.ofNat 1974, Int.ofNat 15364, Int.ofNat 31902, Int.ofNat 31903, Int.ofNat 31904, Int.ofNat 31905, Int.ofNat 31906, Int.ofNat 31907, Int.ofNat 31908, Int.ofNat 31909, Int.ofNat 31910, Int.ofNat 31911, Int.ofNat 31912, Int.ofNat 31913, Int.ofNat 31914, Int.ofNat 31915, Int.ofNat 31916, Int.ofNat 31917, Int.ofNat 31918, Int.ofNat 31919, Int.ofNat 31920, Int.ofNat 31921, Int.ofNat 31922, Int.ofNat 31923] #[2107, 1885, 1901, 928, 292, 1823, 2119, 1884, 1900, 1898, 1883, 1953, 797, 798, 800, 793, 794, 286, 1826, 1141, 1949, 1137, 1827, 1834, 1835, 1836, 294, 2032, 2041, 2038, 2037, 2030, 144, 1787, 1782, 742, 2016, 745, 1139, 1995, 2003, 2001, 1994, 140, 1781, 738, 362, 1852, 2114, 2120, 136, 1969, 1777, 875, 1779, 869, 138],
  .addRup 2122 #[Int.ofNat 589, Int.negSucc 587, Int.negSucc 590, Int.negSucc 15536] #[1951, 770, 772, 773, 774, 766, 366, 776, 1856, 768, 369, 1862, 1857],
  .addRup 2123 #[Int.negSucc 588, Int.negSucc 586, Int.negSucc 587, Int.negSucc 590] #[1770, 1934, 1628, 1629, 1935, 3, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1936, 1948, 1937, 1633, 1938, 1634, 1635, 2069, 427, 1952, 1869, 785, 787, 790, 780, 433, 1875, 786, 788, 778, 429, 1871, 1873, 431, 779],
  .addRup 2124 #[Int.ofNat 15364, Int.ofNat 1974, Int.ofNat 15390] #[2107, 1885, 292, 1823, 2108, 1904, 1905, 1906, 1909, 1897, 1896, 1890, 2118, 1886, 1149, 1143, 1152, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 2121, 288, 1970, 2082, 1828, 887, 2059, 1826, 889, 286, 891, 893, 1833, 2111, 1834, 1835, 1836, 294, 2032, 885, 2041, 494, 2040, 1889, 2031, 1887, 219, 492, 1809, 1804, 1136, 1994, 870, 2001, 364, 2003, 1995, 215, 1803, 2066, 2123, 2122, 362, 1854, 1852],
  .addRup 2125 #[Int.ofNat 589, Int.negSucc 587, Int.negSucc 590, Int.ofNat 15510] #[362, 1852, 1854, 2122],
  .addRup 2126 #[Int.negSucc 590, Int.negSucc 587, Int.ofNat 15217, Int.ofNat 15510] #[2125, 1850, 2123, 1971, 2066, 905, 1803, 895, 1804, 1805, 136, 1809, 217, 1777, 219, 2018, 1778, 2031, 2025, 2026, 2039, 2040, 2023, 2027, 2037, 2041, 2017, 2019, 2030, 2032, 142, 292, 144, 294, 1787, 1836, 1786, 1835, 1785, 1829, 140, 2124, 1994, 290, 2001, 1996, 2002, 2006],
  .addRup 2127 #[Int.negSucc 587, Int.negSucc 15363] #[2107, 794, 290, 1996, 2006, 2004, 1995, 215, 1821, 1837, 1841, 1839, 1822, 1970, 887, 890, 883, 364, 2126, 1953, 800, 797],
  .addRup 2128 #[Int.negSucc 15363, Int.ofNat 15390] #[2107, 290, 2127, 1996, 286, 1950, 2006, 1826, 755, 2002, 2004, 1828, 758, 2001, 1995, 288, 751, 1994, 215, 928, 362, 1951, 140, 2119, 1852, 771, 2114, 763, 2120, 211, 136, 1969, 1799, 1777, 875, 1800, 869, 1807, 138, 1725, 1779, 1781],
  .addRup 2129 #[Int.negSucc 1143, Int.negSucc 1142, Int.ofNat 15098] #[2120, 2059, 136, 870, 1777, 140, 1781, 1779, 138, 1969, 869, 875],
  .addRup 2130 #[Int.negSucc 1142, Int.ofNat 15071] #[2107, 1885, 1901, 1783, 2129, 1971, 905, 928, 1714, 2119, 1884, 1900, 1898, 1883, 1953, 797, 798, 800, 793, 794, 211, 1950, 1799, 755, 1800, 758, 898, 1991, 1040, 2114, 1852, 362, 751, 895, 1034, 290, 136, 138, 1777, 1779, 1780, 1781, 1786, 140, 1787, 1994, 144, 2001, 2030, 2003, 2037, 1995, 2039, 215, 2031, 1807, 219, 1716, 1809, 1830, 1808, 2124, 217, 2019, 2018, 2027, 2026],
  .addRup 2131 #[Int.ofNat 591, Int.negSucc 19944] #[1953, 800, 797],
  .addRup 2132 #[Int.ofNat 15510, Int.negSucc 587, Int.negSucc 590] #[2107, 1885, 1901, 1883, 2127, 1898, 1900, 1884, 1973, 932, 926, 136, 1777, 1778, 2126, 215, 1995, 2003, 2001, 1994, 140, 1785, 2125, 2123, 2066, 1802, 1716, 1830, 2124, 2019, 2027, 2024, 2026, 2023, 2018, 2017, 217, 142, 1808, 1786, 1809, 1787, 219, 144, 2031, 2030, 2039, 2037],
  .addRup 2133 #[Int.ofNat 15364, Int.ofNat 15390] #[2107, 2124, 2019, 1824, 2027, 2024, 2023, 2017, 142, 2130, 2082, 288, 927, 2059, 136, 1828, 1777, 1826, 1778, 1837, 286, 1838, 794, 1842, 2131, 1847, 2132, 1848, 364, 1836, 870, 140, 1785, 1786, 1787, 144, 2030, 2037, 2039, 2031, 1023, 1724, 1802, 2066, 763, 2123, 771, 1951],
  .addRup 2134 #[Int.ofNat 15390] #[2133, 2128],
  .addRup 2135 #[Int.negSucc 587] #[2107, 2134, 2127, 1830, 1716, 1802, 2066, 794, 2131, 2132, 364, 763, 2123, 1951, 771],
  .addRup 2136 #[Int.negSucc 590] #[2107, 1885, 1901, 2134, 1829, 2135, 1950, 755, 757, 758, 759, 760, 761, 753, 294, 1836, 1831, 1835, 1830, 292, 290, 2019, 752, 751, 1996, 2027, 427, 1952, 362, 2006, 2024, 2026, 1869, 785, 1852, 2002, 2004, 2023, 2018, 787, 2001, 1995, 2017, 217, 1994, 215, 142, 140, 1783, 2130, 1781, 1970, 887, 889, 890, 892, 883, 884, 364, 429, 1854, 1871, 1883, 789, 1898, 791, 1899, 1900, 783, 1904, 1884, 434, 1905, 1909, 1897, 1906, 1896, 1890, 1973, 1879, 932, 1874, 1873, 431, 1746, 926, 136, 1777, 1778, 1785, 1786, 1787, 144, 2030, 2037, 2039, 2031, 219, 1809, 1808, 1807, 1806, 213, 2113, 1772, 91, 92, 93, 94, 95, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 118, 119, 1698, 121, 122, 123, 1700, 125, 1752, 127, 1704, 130],
  .addRup 2137 #[Int.negSucc 868, Int.negSucc 15831] #[2107, 2134, 1829, 2135, 1950, 755, 758, 2136, 492, 781, 1953, 1887, 798, 2030, 2037, 2038, 2039, 2041, 2031, 2032, 219, 294, 1809, 1836, 1804, 1831, 1835, 1830, 292, 290, 2019, 751, 1996, 2027, 362, 1951, 2006, 2024, 2026, 1852, 771, 2002, 2004, 2023, 2018, 2001, 1995, 2017, 217, 1994, 215, 142, 1808, 140, 1807, 1783, 1781, 1800, 1806, 1799, 213, 211, 1683, 1975, 2113, 793, 763, 1772, 1974, 1682, 1250, 494, 916, 364, 1971, 91, 1979, 1255, 1889, 1854, 904, 1980, 906, 1981, 909, 1982, 1983, 1984, 1985, 1986, 1987, 1976, 1988, 1977, 1687, 1978, 1688, 1689, 1256, 1259, 1252, 500, 1897, 1892, 1750, 1746, 92, 93, 94, 95, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 118, 119, 120, 1698, 121, 122, 1699, 123, 1700, 125, 1745, 127, 1704, 130],
  .addRup 2138 #[Int.ofNat 15806, Int.negSucc 865, Int.ofNat 1146, Int.negSucc 1850, Int.ofNat 15245, Int.negSucc 15536, Int.ofNat 23792, Int.ofNat 130870, Int.ofNat 130874, Int.ofNat 130875, Int.ofNat 130876] #[2107, 2136, 492, 781, 1887, 494, 916, 1682, 1889, 1893, 1750, 1746, 92, 93, 94, 95, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 118, 119, 120, 1698, 121, 122, 1699, 123, 1700, 125, 1745, 127, 1704, 130],
  .addRup 2139 #[Int.ofNat 31580, Int.ofNat 1146, Int.ofNat 15244, Int.ofNat 15245, Int.negSucc 15536, Int.ofNat 23792] #[2107, 1885, 1907, 2136, 492, 781, 1887, 2002, 2004, 494, 2001, 1995, 1889, 1994, 215, 1890, 140, 1807, 2137, 1806, 144, 213, 1787, 1683, 916, 1975, 1782, 1781, 2113, 1772, 1682, 91, 1974, 1979, 1980, 1981, 1982, 1983, 1984, 1985, 1986, 1987, 1976, 1687, 1988, 1977, 1688, 1978, 1689, 2138, 1908, 1909, 1897, 1892, 1750, 1746, 92, 93, 94, 95, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 118, 119, 120, 1698, 121, 122, 1699, 123, 1700, 125, 1745, 127, 1704, 130],
  .addRup 2140 #[Int.negSucc 865, Int.negSucc 586, Int.negSucc 15537, Int.negSucc 31579] #[2134, 2136, 492, 1953, 1887, 798, 1795, 793, 2006, 1810, 494, 1996, 1889, 290, 1890, 1830, 2137, 1831, 1832, 1716, 1836, 292, 1802, 294, 2019, 1749, 2027, 2024, 2023, 2017, 1341, 2005, 1250, 1811, 1346, 2007, 1255, 1813, 1348, 2008, 1257, 1796, 2009, 2010, 1074, 2012, 2013, 2015, 2000, 1072, 1251, 368, 1861, 1862, 369, 1342],
  .addRup 2141 #[Int.negSucc 31579, Int.negSucc 586, Int.ofNat 1144, Int.negSucc 15536] #[2134, 2136, 492, 1953, 1887, 798, 2006, 1855, 793, 1996, 2140, 494, 290, 138, 1889, 1830, 1784, 1890, 1832, 1716, 2137, 292, 144, 2019, 1787, 2027, 2024, 2023, 2017, 142, 1786, 1780, 1785, 2113, 140, 213, 1994, 1806, 2001, 1807, 2003, 215, 1995],
  .addRup 2142 #[Int.negSucc 15218, Int.negSucc 15288] #[2107, 2134, 1829, 2135, 1950, 755, 758, 2136, 781, 219, 2031, 2039, 2040, 2037, 2041, 2030, 2032, 144, 294, 1787, 1836, 1831, 1835, 1830, 292, 290, 2019, 751, 1996, 2027, 362, 2006, 2024, 2026, 1852, 2002, 2004, 2023, 2018, 2001, 1995, 2017, 217, 1994, 215, 142, 1805, 140, 2130, 1786, 1803, 1970, 1785, 887, 1784, 889, 890, 138, 892, 883, 1772, 1749, 884, 364, 1971, 213, 1972, 1854, 904, 1125, 1261, 91, 918, 906, 1130, 1266, 920, 909, 1131, 1267, 922, 1134, 1270, 924, 1127, 1263, 498, 500, 1897, 1892, 1896, 1750, 1890, 1746, 92, 93, 94, 95, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 118, 119, 1698, 121, 122, 123, 1700, 125, 1752, 127, 1704, 130],
  .addRup 2143 #[Int.negSucc 586, Int.ofNat 1144, Int.negSucc 15536] #[2107, 2134, 2136, 492, 1953, 1887, 798, 1971, 904, 906, 909, 1795, 793, 494, 1889, 1890, 2141, 2002, 2004, 2001, 1995, 1994, 215, 140, 1810, 2137, 144, 1787, 2142, 1809, 1804, 1803, 2139, 1716, 1808, 1830, 217, 290, 2018, 2025, 2023, 2017, 142, 1786, 1785, 1784, 138, 1772, 1682, 1749, 213, 1683, 1125, 91, 1130, 1132, 1126, 433, 1875, 1743, 431, 1746, 92, 93, 94, 95, 96, 97, 98, 1687, 99, 100, 1688, 101, 1689, 103, 105, 107, 109, 111, 113, 115, 117, 118, 119, 120, 1698, 121, 122, 1699, 123, 1700, 125, 1745, 127, 1704, 130],
  .addRup 2144 #[Int.negSucc 15242, Int.ofNat 15245] #[2134, 1802, 1716, 1830, 290, 1996, 2006, 2004, 1995, 215, 1803],
  .addRup 2145 #[Int.negSucc 15243, Int.negSucc 1419, Int.ofNat 15246, Int.negSucc 15289, Int.negSucc 15536, Int.ofNat 23792] #[2107, 2134, 1829, 2136, 492, 1887, 1716, 1725, 1804, 1683, 1830, 290, 1125, 1996, 2006, 2002, 2004, 2001, 1995, 1994, 1130, 140, 1808, 217, 2018, 2026, 2027, 2019, 292, 1835, 1836, 294, 1781, 2113, 1772, 1682, 91, 1132, 1126, 433, 1875, 2025, 2023, 2017, 142, 2130, 1970, 887, 889, 891, 893, 885, 494, 1889, 1743, 431, 1746, 92, 93, 94, 95, 96, 97, 98, 1687, 99, 100, 1688, 101, 1689, 103, 105, 107, 109, 111, 113, 115, 117, 118, 119, 120, 1698, 121, 122, 1699, 123, 1700, 125, 1745, 127, 1704, 130],
  .addRup 2146 #[Int.ofNat 15246, Int.negSucc 15240, Int.negSucc 15536, Int.ofNat 23792] #[2134, 1855, 1800, 1804, 2144, 1801, 213, 1814, 2145, 1807, 215, 1995, 2004, 2006, 1996, 290, 1830, 1831, 1832, 1836, 292, 294, 2019, 1261, 2032, 1352, 2027, 2041, 2026, 2040, 2018, 2031, 1266, 1357, 1268, 1359, 1262, 1353, 368, 369, 1861, 1862],
  .addRup 2147 #[Int.negSucc 15534, Int.ofNat 15510] #[2107, 2134, 1829, 2135, 286, 1826, 2136, 781, 1850, 1971, 1854, 904, 1855, 2143, 211, 1799, 906, 909, 2146, 1809, 219, 2031, 2040, 2041, 2032, 294, 1836, 1831, 1830, 290, 1996, 2006, 2002, 2004, 2001, 1995, 1994, 140, 1717, 2039, 2037, 2030, 144, 1787, 1835, 292, 2019, 2027, 2024, 2023, 2017, 142, 2130, 1786, 1970, 1785, 887, 1784, 889, 138, 892, 1772, 884, 217, 1972, 1805, 918, 2144, 1749, 213, 1261, 91, 1266, 920, 1125, 1267, 922, 1130, 1270, 924, 1131, 1263, 1134, 500, 1127, 1897, 498, 1892, 1896, 1750, 1890, 1746, 92, 93, 94, 95, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 118, 119, 1698, 121, 122, 123, 1700, 125, 127, 130, 1704, 1752],
  .addRup 2148 #[Int.ofNat 15510] #[2107, 2134, 2135, 1950, 755, 757, 758, 760, 2136, 492, 1887, 1859, 1850, 2147, 1852, 362, 751, 290, 1830, 1831, 1832, 1716, 1836, 292, 294, 2019, 752, 2032, 2027, 427, 2041, 2024, 1869, 2038, 2023, 2037, 2017, 2030, 142, 144, 1787, 1786, 1780, 1971, 1952, 2130, 1970, 887, 889, 892, 884, 905, 785, 891, 429, 895, 787, 893, 1871, 136, 790, 885, 1777, 780, 494, 1778, 1785, 140, 1994, 2001, 2003, 1995, 215, 1807, 1800, 1806, 1799, 213, 211, 2113, 1772, 91, 433, 1889, 2002, 1683, 2140, 1860, 366, 92, 1682, 1875, 1873, 431, 93, 94, 95, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 118, 119, 1698, 121, 122, 123, 1700, 125, 127, 130, 1704, 96, 98, 100, 120, 1687, 1688, 1689, 1699, 1745],
  .addRup 2149 #[Int.negSucc 15508, Int.negSucc 865] #[2148, 1863, 362, 1864, 1034, 1865, 1851, 1040, 1991],
  .addRup 2150 #[Int.negSucc 15391, Int.negSucc 1419] #[2107, 2135, 1950, 755, 757, 760, 2148, 364, 1831, 1832, 1716, 1836, 292, 294, 2019, 2032, 2027, 2041, 2024, 2038, 2023, 2037, 2017, 2030, 142, 144, 1787, 1786, 752, 1261, 1352, 2026, 2040, 1783, 2129, 1970, 887, 1780, 427, 2018, 2031, 896, 889, 2113, 1869, 1266, 1357, 892, 2149, 1772, 1268, 1359, 884, 1852, 1849, 1951, 771, 763, 211, 1799, 1800, 1807, 215, 91, 1719, 1853, 1262, 1353, 431, 368, 369, 1862, 1861, 1860, 366, 92, 93, 94, 95, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 118, 119, 1698, 121, 122, 123, 1700, 125, 1715, 127, 1704, 130],
  .addRup 2151 #[Int.negSucc 1972] #[2135, 1950, 755, 758, 2148, 364, 751, 883, 1996, 1951, 2006, 771, 2004, 1995, 215, 763, 211, 1799, 1800, 1807, 1725, 2129, 1970, 890, 887],
  .addEmpty 2152 #[2134, 2151, 290, 1830, 1831, 1832, 1716, 2150, 1836, 292, 1802, 213, 294, 2019, 1806, 1749, 2032, 2027, 1807, 138, 2041, 2024, 215, 1784, 2038, 2023, 1995, 2037, 2017, 2003, 2030, 142, 2001, 144, 1994, 1787, 140, 1786, 1785]
]

def formula : CNF Nat := DsrgRank.Sat.ofLists clauses

set_option maxHeartbeats 0 in

theorem formula_unsat : formula.Unsat :=
  DsrgRank.Sat.checkTrie_sound clauses proof (by decide +kernel)

theorem unsat_of_superset (F : CNF Nat) (h : ∀ c ∈ formula.clauses, c ∈ F.clauses) :
    F.Unsat :=
  DsrgRank.Sat.unsat_of_subset h formula_unsat

end DsrgRank.Sat.Case28Free
