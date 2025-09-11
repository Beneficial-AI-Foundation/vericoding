-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValid (formula : List Nat) : Bool := sorry

theorem valid_formula_characterization (formula : List Nat) :
  isValid formula = ¬(
    ((1 ∈ formula) ∧ (2 ∈ formula)) ∨
    ((3 ∈ formula) ∧ (4 ∈ formula)) ∨
    ((5 ∈ formula) ∧ (6 ∉ formula)) ∨
    ((6 ∈ formula) ∧ (5 ∉ formula)) ∨
    ((7 ∉ formula) ∧ (8 ∉ formula))
  ) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem out_of_range_elements (formula : List Nat) :
  (∀ x ∈ formula, x < 1 ∨ x > 8) →
  isValid formula = isValid [] := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval isValid [1, 3, 7]

/-
info: False
-/
-- #guard_msgs in
-- #eval isValid [7, 1, 2, 3]

/-
info: True
-/
-- #guard_msgs in
-- #eval isValid [1, 5, 6, 7, 3]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded