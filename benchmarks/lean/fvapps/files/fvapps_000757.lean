-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_sequence (D: Nat) : List Nat := sorry

theorem sequence_elements_positive (D: Nat) (x: Nat) :
  x ∈ solve_sequence D → x > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_elements_bounded (D: Nat) (x: Nat) :
  x ∈ solve_sequence D → x ≤ 100000 := sorry
-- </vc-theorems>