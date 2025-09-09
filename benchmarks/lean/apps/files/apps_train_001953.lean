-- <vc-helpers>
-- </vc-helpers>

def min_ops_to_make_nondecreasing (n : Nat) (m : Nat) (A : List Nat) : Nat :=
sorry

theorem min_ops_result_range {n m : Nat} {A : List Nat} 
  (hn : n > 0) (hm : m > 0) (hA : A.length > 0) :
  let result := min_ops_to_make_nondecreasing n m A
  0 ≤ result ∧ result ≤ m :=
sorry

theorem sorted_array_needs_zero_ops {n m : Nat}
  (hn : n > 0) (hm : m > 0) :
  let A := List.range (min n m)
  min_ops_to_make_nondecreasing A.length m A = 0 :=
sorry

theorem single_value_array_needs_zero_ops {n m : Nat} {x : Nat}
  (hm : m > 0) :
  min_ops_to_make_nondecreasing 1 m [x % m] = 0 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_ops_to_make_nondecreasing 5 3 [0, 0, 0, 1, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_ops_to_make_nondecreasing 5 7 [0, 6, 1, 3, 2]

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_ops_to_make_nondecreasing 10 10 [5, 0, 5, 9, 4, 6, 4, 5, 0, 0]

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible