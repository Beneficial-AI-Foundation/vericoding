-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPowerOfTwo (n : Nat) : Bool := sorry

def solve_beautiful_permutation (n : Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element_case {n : Nat} (h : n = 1) :
  solve_beautiful_permutation n = [1] := sorry

theorem power_of_two_case {n : Nat} (h : isPowerOfTwo n = true) :
  solve_beautiful_permutation n = [0] := sorry  -- Using 0 instead of -1 since we're working with Nat

theorem length_matches_input {n : Nat} (h : n ≠ 1 ∧ isPowerOfTwo n = false) :
  (solve_beautiful_permutation n).length = n := sorry  

theorem permutation_elements {n : Nat} (h : n ≠ 1 ∧ isPowerOfTwo n = false) (i : Nat) (hi : i < n) :
  ∃ j, j < (solve_beautiful_permutation n).length ∧ 
       (solve_beautiful_permutation n).get ⟨j, by sorry⟩ = i + 1 := sorry
-- </vc-theorems>