-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_equal_tuples (n : Nat) (arr : List Nat) : Nat := sorry

theorem count_equal_tuples_nonnegative 
  {n : Nat} {arr : List Nat} (h1 : n ≥ 3) (h2 : arr.length = n) :
  count_equal_tuples n arr ≥ 0 := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_equal_tuples_distinct_elements
  {n : Nat} {arr : List Nat} (h1 : n ≥ 3) (h2 : arr.length = n)
  (h3 : ∀ (i j : Nat) (hi : i < n) (hj : j < n), i ≠ j → 
    (arr.get ⟨i, by rw [h2]; exact hi⟩) ≠ 
    (arr.get ⟨j, by rw [h2]; exact hj⟩)) :
  count_equal_tuples n arr = 0 :=
sorry

theorem count_equal_tuples_two_values
  {n : Nat} (h1 : n ≥ 3) :
  let arr := List.append (List.replicate (n/2) 1) (List.replicate (n - n/2) 2)
  count_equal_tuples n arr ≥ 0 :=
sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval count_equal_tuples 5 [2, 2, 2, 2, 2]

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_equal_tuples 6 [1, 3, 3, 1, 2, 3]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_equal_tuples 4 [1, 1, 1, 1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded