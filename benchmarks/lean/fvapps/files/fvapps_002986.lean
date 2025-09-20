-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_happy (n : Nat) : Bool := sorry

def happy_numbers (n : Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem happy_numbers_consistent {n : Nat} (h : n > 0) :
  happy_numbers n = happy_numbers n := sorry

theorem happy_numbers_specific_values :
  1 ∈ happy_numbers 1 ∧
  1 ∈ happy_numbers 100 ∧
  7 ∈ happy_numbers 100 ∧
  10 ∈ happy_numbers 100 ∧
  13 ∈ happy_numbers 100 ∧
  19 ∈ happy_numbers 100 ∧
  4 ∉ happy_numbers 100 := sorry
-- </vc-theorems>