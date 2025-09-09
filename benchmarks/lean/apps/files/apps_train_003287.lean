def sum_list (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | x :: xs => x + sum_list xs

-- <vc-helpers>
-- </vc-helpers>

def sum_times_tables (tables : List Int) (min_val max_val : Int) : Int :=
  sorry

theorem sum_times_tables_zero_sum {tables : List Int} {min_val max_val : Int} :
  (sum_list tables = 0) → sum_times_tables tables min_val max_val = 0 :=
sorry

theorem sum_times_tables_equal_bounds {tables : List Int} {val : Int} :
  sum_times_tables tables val val = sum_list tables * val :=
sorry

theorem sum_times_tables_symmetric {tables : List Int} {min_val max_val : Int} :
  sum_times_tables tables min_val max_val = sum_times_tables tables min_val max_val :=
sorry

theorem sum_times_tables_zero_range {tables : List Int} :
  sum_times_tables tables 0 0 = 0 * sum_list tables :=
sorry

theorem sum_times_tables_positive {tables : List Int} {val : Int} :
  (∀ x ∈ tables, x > 0) → val > 0 → sum_times_tables tables 1 val ≥ 0 :=
sorry

/-
info: 30
-/
-- #guard_msgs in
-- #eval sum_times_tables [2, 3] 1 3

/-
info: 9
-/
-- #guard_msgs in
-- #eval sum_times_tables [1, 3, 5] 1 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval sum_times_tables [-2, 2] -1 3

-- Apps difficulty: introductory
-- Assurance level: unguarded