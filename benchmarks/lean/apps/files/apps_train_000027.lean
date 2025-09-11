-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_moves_to_odd (arrays : List (List Nat)) : List Nat := sorry

def countTrailingZeros (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_same_length_as_input (arrays : List (List Nat)) :
  List.length (min_moves_to_odd arrays) = List.length arrays :=
  sorry

theorem result_is_non_negative (arrays : List (List Nat)) :
  ∀ x ∈ min_moves_to_odd arrays, x ≥ 0 :=
  sorry

/-
info: [4]
-/
-- #guard_msgs in
-- #eval min_moves_to_odd [[40, 6, 40, 3, 20, 1]]

/-
info: [10]
-/
-- #guard_msgs in
-- #eval min_moves_to_odd [[1024]]

/-
info: [4]
-/
-- #guard_msgs in
-- #eval min_moves_to_odd [[2, 4, 8, 16]]

/-
info: [0]
-/
-- #guard_msgs in
-- #eval min_moves_to_odd [[3, 1, 7]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible