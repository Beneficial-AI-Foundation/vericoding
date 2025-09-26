-- <vc-preamble>
def List.minimum (l : List Nat) : Option Nat :=
  sorry

def List.maximum (l : List Nat) : Option Nat :=
  sorry

def List.sum (l : List Nat) : Nat :=
  sorry

def List.log2 (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def combine_fruits (fruits : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem combine_fruits_empty_singleton {fruits : List Nat} 
  (h : fruits.length ≤ 1) : combine_fruits fruits = 0 := by
  sorry

theorem combine_fruits_nonneg {fruits : List Nat} :
  combine_fruits fruits ≥ 0 := by
  sorry

theorem combine_fruits_lower_bound {fruits : List Nat} {min1 min2 : Nat}
  (h : fruits.length ≥ 2)
  (h1 : fruits.minimum = some min1)
  (h2 : (fruits.tail).minimum = some min2) :
  combine_fruits fruits ≥ min1 + min2 := by
  sorry

theorem combine_fruits_upper_bound {fruits : List Nat} 
  (h : fruits ≠ []) :
  combine_fruits fruits ≤ fruits.sum * (fruits.length.log2) := by
  sorry

theorem combine_fruits_monotone {fruits : List Nat} {x maxVal : Nat}
  (h : fruits.length ≥ 2)
  (h2 : fruits.maximum = some maxVal)
  (h3 : x > maxVal) :
  combine_fruits (fruits ++ [x]) ≥ combine_fruits fruits := by
  sorry

/-
info: 15
-/
-- #guard_msgs in
-- #eval combine_fruits [1, 2, 9]

/-
info: 0
-/
-- #guard_msgs in
-- #eval combine_fruits [100]

/-
info: 111
-/
-- #guard_msgs in
-- #eval combine_fruits [4, 3, 5, 6, 10, 20]
-- </vc-theorems>