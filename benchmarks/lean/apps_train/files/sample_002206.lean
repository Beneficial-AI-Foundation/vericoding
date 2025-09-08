/-
You are given $n$ arrays that can have different sizes. You also have a table with $w$ columns and $n$ rows. The $i$-th array is placed horizontally in the $i$-th row. You can slide each array within its row as long as it occupies several consecutive cells and lies completely inside the table.

You need to find the maximum sum of the integers in the $j$-th column for each $j$ from $1$ to $w$ independently.

 [Image] Optimal placements for columns $1$, $2$ and $3$ are shown on the pictures from left to right. 

Note that you can exclude any array out of a column provided it remains in the window. In this case its value is considered to be zero.

-----Input-----

The first line contains two integers $n$ ($1 \le n \le 10^{6}$) and $w$ ($1 \le w \le 10^{6}$) — the number of arrays and the width of the table.

Each of the next $n$ lines consists of an integer $l_{i}$ ($1 \le l_{i} \le w$), the length of the $i$-th array, followed by $l_{i}$ integers $a_{i1}, a_{i2}, \ldots, a_{il_i}$ ($-10^{9} \le a_{ij} \le 10^{9}$) — the elements of the array.

The total length of the arrays does no exceed $10^{6}$.

-----Output-----

Print $w$ integers, the $i$-th of them should be the maximum sum for column $i$.

-----Examples-----
Input
3 3
3 2 4 8
2 2 5
2 6 3

Output
10 15 16 

Input
2 2
2 7 8
1 -8

Output
7 8 

-----Note-----

Illustration for the first example is in the statement.
-/

-- <vc-helpers>
-- </vc-helpers>

def maximum (l : List Int) : Int := sorry

def slidemax (nums : List Int) (k : Nat) : List Int := sorry

theorem slidemax_matches_window_max
  (nums : List Int) (k : Nat)
  (h1 : 0 < k) 
  (h2 : k ≤ nums.length) :
  slidemax nums k = 
    (List.range (nums.length + 1 - k)).map (fun i =>
      maximum (List.take k (List.drop i nums))) := sorry

theorem slidemax_length
  (nums : List Int) (k : Nat)
  (h1 : 0 < k)
  (h2 : k ≤ nums.length) :
  (slidemax nums k).length = nums.length + 1 - k := sorry

/-
info: [10, 15, 16]
-/
-- #guard_msgs in
-- #eval solve 3 3 [[3, 2, 4, 8], [2, 2, 5], [2, 6, 3]]

/-
info: [7, 8]
-/
-- #guard_msgs in
-- #eval solve 2 2 [[2, 7, 8], [1, -8]]

-- Apps difficulty: competition
-- Assurance level: unguarded