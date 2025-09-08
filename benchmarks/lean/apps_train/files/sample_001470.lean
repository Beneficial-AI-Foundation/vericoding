/-
The Chef has a huge square napkin of size 2n X 2n. He folds the napkin n-3 times. Each time he folds its bottom side over its top side, and then its right side over its left side. After each fold, the side length of the napkin is reduced by half. The Chef continues folding until there remains a 8x8 sheet, lying flat on a table.
Oh, did I forget to mention that the Chef was cooking a new brown colored curry while folding the napkin. He drops some brown colored gravy onto some cells in the folded 8x8 napkin. When he drops the gravy, it soaks through all the cells below it.
Now the Chef unfolds the napkin to its original size. There are now many curry stained brown colored cells in the napkin. They form several separate regions, each of which is connected. Could you help the Chef count how many regions of brown cells are there in the napkin?
Note that two cells are adjacent if they share a common edge (they are not considered adjacent if they only share a corner). Two cells are connected if we can go from one cell to the other via adjacent cells. A region is a maximal set of cells such that every two of its cells are connected.
Please see the example test case for more details.

-----Input-----
The first line contains t, the number of test cases (about 50). Then t test cases follow. Each test case has the following form:
- The first line contains N (3 ≤ N ≤ 109)
- Then, 8 lines follow. Each line is a string of 8 characters, 0 or 1, where 1 denotes a stained brown cell in the folded napkin.

-----Output-----
For each test case, print a single number that is the number of disconnected brown regions in the unfolded napkin. Since the result may be a very large number, you only need to print its remainder when dividing by 21945.

-----Example-----
Input:
3
3
01000010
11000001
00000000
00011000
00011000
00010100
00001000
00000000
4
01000010
11000001
00000000
00011000
00011000
00010100
00001000
00000000
1000000000
11111111
11111111
11111111
11111111
11111111
11111111
11111111
11111111

Output:
6
22
1

-----Output details-----

Case 1 and 2: There are 6 brown regions in the 8x8 napkin. If we unfold it once, it has 22 brown regions: 11 regions in the top half and 11 regions in the bottom half (as shown in the figure above).
Case 3: All cells of the napkin are stained, so there is always one brown region, no matter how many times the Chef unfolds the napkin.
-/

-- <vc-helpers>
-- </vc-helpers>

def count_brown_regions (n : Nat) (grid : List String) : Nat := sorry

def empty_grid : List String := ["00000000", "00000000", "00000000", "00000000", 
                               "00000000", "00000000", "00000000", "00000000"]

theorem count_brown_regions_bounds {n : Nat} {grid : List String} 
  (h1 : n ≥ 3) : 
  0 ≤ count_brown_regions n grid ∧ count_brown_regions n grid < 21945 := sorry

theorem empty_grid_gives_zero : 
  count_brown_regions 3 empty_grid = 0 := sorry

theorem grid_constraints (grid : List String) 
  (h1 : grid.length = 8)
  (h2 : ∀ row ∈ grid, row.length = 8)
  (h3 : ∀ row ∈ grid, ∀ c ∈ row.data, c = '0' ∨ c = '1') :
  True := sorry

theorem output_modulo {n : Nat} {grid : List String}
  (h1 : n ≥ 3) :
  0 ≤ count_brown_regions n grid ∧ count_brown_regions n grid < 21945 := sorry

theorem idempotency {n : Nat} {grid : List String}
  (h1 : n ≥ 3) :
  count_brown_regions n grid = count_brown_regions n grid := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_brown_regions 3 ["01000010", "11000001", "00000000", "00011000", "00011000", "00010100", "00001000", "00000000"]

/-
info: 22
-/
-- #guard_msgs in
-- #eval count_brown_regions 4 ["01000010", "11000001", "00000000", "00011000", "00011000", "00010100", "00001000", "00000000"]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_brown_regions 1000000000 ["11111111", "11111111", "11111111", "11111111", "11111111", "11111111", "11111111", "11111111"]

-- Apps difficulty: interview
-- Assurance level: unguarded