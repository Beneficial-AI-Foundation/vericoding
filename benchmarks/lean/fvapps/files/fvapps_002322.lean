-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countTrailingOnes : List Nat → Nat
  | [] => 0
  | xs => sorry

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
-- </vc-theorems>