-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_magic_jackets (n: Nat) (counts: List Nat) : Int := sorry

theorem all_zeros (n: Nat) : 
  n ≥ 2 → solve_magic_jackets n (List.replicate n 0) = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_n_minus_one (n: Nat) :
  n ≥ 2 → solve_magic_jackets n (List.replicate n (n-1)) = 0 := sorry

theorem valid_pattern (n: Nat) : 
  n ≥ 3 →
  solve_magic_jackets n (List.replicate (n-1) (n-2) ++ [n-1]) = 1 := sorry 

theorem invalid_difference (n: Nat) (base diff: Nat) :
  n ≥ 2 →
  diff ≥ 2 →
  solve_magic_jackets n (List.replicate (n-1) base ++ [base + diff]) = -1 := sorry

theorem length_mismatch (n: Nat) (counts: List Nat) :
  n ≥ 2 →
  List.length counts ≠ n →
  let result := solve_magic_jackets n counts
  result = -1 ∨ result = 0 ∨ result = n ∨ result = 1 := sorry
-- </vc-theorems>