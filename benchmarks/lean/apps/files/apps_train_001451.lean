-- <vc-preamble>
def make_valid_bracket_sequence (n : Nat) : List Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def analyze_brackets (n : Nat) (brackets : List Nat) : Nat × Nat × Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minimal_valid_case :
  analyze_brackets 2 [1,2] = (1,1,2,1) :=
sorry

theorem nested_depth_increases :
  (analyze_brackets 4 [1,1,2,2]).1 = 2 :=
sorry

/-
info: (2, 4, 6, 9)
-/
-- #guard_msgs in
-- #eval analyze_brackets 20 [1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 2]

/-
info: (1, 1, 2, 1)
-/
-- #guard_msgs in
-- #eval analyze_brackets 2 [1, 2]

/-
info: (2, 2, 6, 1)
-/
-- #guard_msgs in
-- #eval analyze_brackets 8 [1, 1, 2, 1, 2, 2, 1, 2]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible