-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def prod2sum (a b c d: Int) : List (List Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem prod2sum_output_length (a b c d : Int) :
  let result := prod2sum a b c d
  1 ≤ result.length ∧ result.length ≤ 2 := sorry

theorem prod2sum_sublist_length (a b c d : Int) :
  let result := prod2sum a b c d
  ∀ sublist ∈ result, sublist.length = 2 := sorry

theorem prod2sum_nonneg_values (a b c d : Int) :
  let result := prod2sum a b c d
  ∀ sublist ∈ result, ∀ x ∈ sublist, 0 ≤ x := sorry

theorem prod2sum_sublists_sorted (a b c d : Int) :
  let result := prod2sum a b c d
  ∀ sublist ∈ result, (sublist.get! 0) ≤ (sublist.get! 1) := sorry

theorem prod2sum_list_sorted (a b c d : Int) :
  let result := prod2sum a b c d
  result.length = 2 → (result.get! 0) ≤ (result.get! 1) := sorry

theorem prod2sum_reversible (a b c d : Int) :
  (prod2sum a b c d).length = (prod2sum c d a b).length := sorry

/-
info: [[1, 7], [5, 5]]
-/
-- #guard_msgs in
-- #eval prod2sum 1 2 1 3

/-
info: [[2, 23], [7, 22]]
-/
-- #guard_msgs in
-- #eval prod2sum 2 3 4 5

/-
info: [[2, 8]]
-/
-- #guard_msgs in
-- #eval prod2sum 1 1 3 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible