-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isOddHeavy (lst : List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_list_not_odd_heavy :
  isOddHeavy [] = false :=
sorry

theorem all_evens_not_odd_heavy (lst : List Int) :
  (lst ≠ []) → (∀ x ∈ lst, x % 2 = 0) → isOddHeavy lst = false :=
sorry

theorem odd_heavy_characterization (lst : List Int) :
  (isOddHeavy lst = true) ↔
  (∃ x ∈ lst, x % 2 ≠ 0) ∧ 
  (∀ e ∈ lst, e % 2 = 0 → 
   ∀ o ∈ lst, o % 2 ≠ 0 → o > e) :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_odd_heavy [0, 2, 19, 4, 4]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_odd_heavy [0, 0, 0, 0]

/-
info: True
-/
-- #guard_msgs in
-- #eval is_odd_heavy [-1, -2, 21]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded