/-
Due to the COVID pandemic, there has been an increase in the number of cases if a hospital. The management has decided to clear a large square area for the patients and arrange for beds. But the beds can't be too near to each other.
The area is of dimension $N$ x $N$
The whole area is already divided into blocks. $1$ means there's a bed in the block, $0$ denotes there isn't. Note, beds placed on consecutive diagonal blocks are safe.
This is a SAFE example:
1 0
0 1
This is an UNSAFE example:
0 1 1
0 0 0
1 0 0
To avoid spreading the virus even further, you have to make sure no two adjacent blocks have beds in them. This is done to maintain distance between beds.
Return an output of "SAFE" if you find the workers have arranged the beds with due consideration to the distance needed. Return "UNSAFE" otherwise.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Next line contains $N$.
- Next $N$ lines will contain $N$ number of space-separated integers $Ai$ which make denote the beds in the area.

-----Output:-----
For each test case, output in a single line whether the total arrangement is "SAFE" or "UNSAFE". Even if there's a single unsafe bed in the whole area, report the whole area as "UNSAFE".

-----Constraints-----
- $1 \leq T \leq 100$
- $0 \leq Ai \leq 1$
- $2 \leq N \leq 100$

-----Subtasks-----
- 30 points : $1 \leq N \leq 7$
- 70 points : Original constraints

-----Sample Input:-----
2
4
1 0 1 0
0 0 0 1
0 1 0 0
1 0 0 1
4
1 0 1 0
0 0 0 0
1 0 1 1
0 1 0 0

-----Sample Output:-----
SAFE
UNSAFE

-----EXPLANATION:-----
Beds placed on blocks diagonally are not a problem.
-/

-- <vc-helpers>
-- </vc-helpers>

def check_bed_arrangement (n : Nat) (grid : List (List Nat)) : String :=
  sorry

theorem empty_grid_safe {n : Nat} (h : 2 ≤ n) (h2 : n ≤ 10) :
  let grid := List.replicate n (List.replicate n 0)
  check_bed_arrangement n grid = "SAFE" :=
sorry

theorem single_bed_safe {n : Nat} (h : 2 ≤ n) (h2 : n ≤ 10) :
  let grid := List.replicate n (List.replicate n 0)
  check_bed_arrangement n grid = "SAFE" :=
sorry

theorem adjacent_horizontal_beds_unsafe {n : Nat} (h : 2 ≤ n) (h2 : n ≤ 10)
  (row : Nat) (col : Nat) :
  let row' := row % n
  let col' := col % (n-1)
  let grid := List.replicate n (List.replicate n 0)
  check_bed_arrangement n grid = "UNSAFE" :=
sorry

theorem adjacent_vertical_beds_unsafe {n : Nat} (h : 2 ≤ n) (h2 : n ≤ 10)
  (row : Nat) (col : Nat) :
  let row' := row % (n-1)
  let col' := col % n
  let grid := List.replicate n (List.replicate n 0)
  check_bed_arrangement n grid = "UNSAFE" :=
sorry

theorem diagonal_beds_safe {n : Nat} (h : 2 ≤ n) (h2 : n ≤ 10) :
  let grid := List.replicate n (List.replicate n 0)
  check_bed_arrangement n grid = "SAFE" :=
sorry

/-
info: 'SAFE'
-/
-- #guard_msgs in
-- #eval check_bed_arrangement 4 [[1, 0, 1, 0], [0, 0, 0, 1], [0, 1, 0, 0], [1, 0, 0, 1]]

/-
info: 'UNSAFE'
-/
-- #guard_msgs in
-- #eval check_bed_arrangement 4 [[1, 0, 1, 0], [0, 0, 0, 0], [1, 0, 1, 1], [0, 1, 0, 0]]

/-
info: 'SAFE'
-/
-- #guard_msgs in
-- #eval check_bed_arrangement 2 [[1, 0], [0, 1]]

-- Apps difficulty: interview
-- Assurance level: unguarded