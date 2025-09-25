-- <vc-preamble>
def List.sum (xs : List Nat) : Nat := 
  xs.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_christmas_boxes (n: Nat) (boxes: List Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_christmas_boxes_result_valid {n: Nat} {boxes: List Nat} :
  let result := solve_christmas_boxes n boxes 
  result ≥ -1 :=
sorry

theorem solve_christmas_boxes_single_one_impossible {n: Nat} {boxes: List Nat} :
  boxes.length = n →
  boxes.sum = 1 →
  solve_christmas_boxes n boxes = -1 :=
sorry

theorem solve_christmas_boxes_result_positive {n: Nat} {boxes: List Nat} :
  let result := solve_christmas_boxes n boxes
  result ≠ -1 → result > 0 :=
sorry

theorem solve_christmas_boxes_length_matches {n: Nat} {boxes: List Nat} :
  solve_christmas_boxes n boxes = solve_christmas_boxes n boxes →
  boxes.length = n :=
sorry

theorem solve_christmas_boxes_valid_values {n: Nat} {boxes: List Nat} :
  solve_christmas_boxes n boxes = solve_christmas_boxes n boxes →
  ∀ x ∈ boxes, x = 0 ∨ x = 1 :=
sorry

theorem solve_christmas_boxes_all_ones {n: Nat} :
  let boxes := List.replicate n 1
  solve_christmas_boxes n boxes ≥ -1 :=
sorry

theorem solve_christmas_boxes_all_zeros {n: Nat} :
  let boxes := List.replicate n 0
  solve_christmas_boxes n boxes = -1 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_christmas_boxes 3 [1, 0, 1]

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_christmas_boxes 1 [1]

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve_christmas_boxes 6 [1, 1, 0, 0, 0, 1]
-- </vc-theorems>