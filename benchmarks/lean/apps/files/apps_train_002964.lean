def is_lucky (n : Nat) : Bool :=
  sorry

def sum_of_digits (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def concat_digits (a b : Nat) : Nat :=
  sorry

theorem lucky_digit_sum_property (n : Nat) :
  is_lucky n = (sum_of_digits n = 0 ∨ sum_of_digits n % 9 = 0) :=
sorry

theorem lucky_concatenation (n : Nat) :
  is_lucky n → (
    is_lucky (concat_digits n 9) ∧  
    is_lucky (concat_digits n 99)
  ) :=
sorry

theorem lucky_edge_cases :
  is_lucky 0 ∧ is_lucky 9 ∧ is_lucky 99 :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_lucky 1892376

/-
info: False
-/
-- #guard_msgs in
-- #eval is_lucky 189237

/-
info: True
-/
-- #guard_msgs in
-- #eval is_lucky 0

-- Apps difficulty: introductory
-- Assurance level: unguarded