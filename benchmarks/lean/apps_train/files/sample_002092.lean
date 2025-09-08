/-
Jzzhu has picked n apples from his big apple tree. All the apples are numbered from 1 to n. Now he wants to sell them to an apple store. 

Jzzhu will pack his apples into groups and then sell them. Each group must contain two apples, and the greatest common divisor of numbers of the apples in each group must be greater than 1. Of course, each apple can be part of at most one group.

Jzzhu wonders how to get the maximum possible number of groups. Can you help him?

-----Input-----

A single integer n (1 ≤ n ≤ 10^5), the number of the apples.

-----Output-----

The first line must contain a single integer m, representing the maximum number of groups he can get. Each of the next m lines must contain two integers — the numbers of apples in the current group.

If there are several optimal answers you can print any of them.

-----Examples-----
Input
6

Output
2
6 3
2 4

Input
9

Output
3
9 3
2 4
6 8

Input
2

Output
0
-/

-- <vc-helpers>
-- </vc-helpers>

def find_max_pairs (n: Nat) : List (Nat × Nat) := sorry

theorem find_max_pairs_range {n: Nat} (h: n ≥ 2) :
  let result := find_max_pairs n
  let flat_nums := result.bind (λ p => [p.1, p.2])
  ∀ x ∈ flat_nums, 1 ≤ x ∧ x ≤ n := 
sorry

theorem find_max_pairs_unique {n: Nat} (h: n ≥ 2) :
  let result := find_max_pairs n
  let flat_nums := result.bind (λ p => [p.1, p.2])
  ∀ x ∈ flat_nums, ∀ y ∈ flat_nums, x ≠ y → 
    flat_nums.indexOf x ≠ flat_nums.indexOf y :=
sorry

/-
info: expected_groups
-/
-- #guard_msgs in
-- #eval len find_max_pairs(n)

/-
info: 2
-/
-- #guard_msgs in
-- #eval len pair

-- Apps difficulty: competition
-- Assurance level: unguarded