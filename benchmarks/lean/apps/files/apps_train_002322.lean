-- <vc-preamble>
def countTrailingOnes : List Nat → Nat
  | [] => 0
  | xs => sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_one_bit_character (bits : List Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ends_with_zero {bits : List Nat} (h : bits ≠ []) : 
  bits.getLast (by exact h) = 0 → 
  is_one_bit_character bits = true ∨ is_one_bit_character bits = false :=
sorry

theorem all_zeros_is_true {bits : List Nat} (h : bits ≠ []) :
  (bits.all (fun x => x = 0)) →
  is_one_bit_character bits = true :=
sorry

theorem trailing_ones_parity {bits : List Nat} (h : bits.length ≥ 2) :
  is_one_bit_character bits = (countTrailingOnes (bits.dropLast) % 2 = 0) :=
sorry

theorem edge_cases_hold :
  (is_one_bit_character [0] = true) ∧ 
  (is_one_bit_character [0, 0] = true) :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_one_bit_character [1, 0, 0]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_one_bit_character [1, 1, 1, 0]

/-
info: True
-/
-- #guard_msgs in
-- #eval is_one_bit_character [0, 0]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded