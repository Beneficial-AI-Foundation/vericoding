def find_best_value (arr : List Nat) (target : Nat) : Nat :=
  sorry

def sum_capped_vals (arr : List Nat) (cap : Nat) : Nat :=
  sorry

def list_maximum (arr : List Nat) (h : arr ≠ []) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def abs (n : Int) : Nat :=
  sorry

theorem find_best_value_bounds {arr : List Nat} {target : Nat} (h : arr ≠ []) :
  let result := find_best_value arr target
  0 ≤ result ∧ result ≤ list_maximum arr h :=
sorry

theorem find_best_value_minimizes {arr : List Nat} {target : Nat} (h : arr ≠ []) :
  let result := find_best_value arr target
  let curr_diff := abs (sum_capped_vals arr result - target)
  let less := max 0 (result - 1)
  let more := min (list_maximum arr h) (result + 1)
  curr_diff ≤ abs (sum_capped_vals arr less - target) ∧
  curr_diff ≤ abs (sum_capped_vals arr more - target) := 
sorry

theorem find_best_value_target_one {arr : List Nat} (h : arr ≠ []) :
  let result := find_best_value arr 1
  result = 0 ∨ result = 1 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_best_value [4, 9, 3] 10

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_best_value [2, 3, 5] 10

/-
info: 11361
-/
-- #guard_msgs in
-- #eval find_best_value [60864, 25176, 27249, 21296, 20204] 56803

-- Apps difficulty: interview
-- Assurance level: guarded