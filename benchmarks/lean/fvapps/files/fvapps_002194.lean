-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (pairs : List (Nat × Nat)) : Nat := sorry 

theorem solve_non_negative (n : Nat) (pairs : List (Nat × Nat)) :
  solve n pairs ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_upper_bound (n : Nat) (pairs : List (Nat × Nat)) :
  solve n pairs ≤ pairs.foldl (fun acc p => acc + p.1) 0 := sorry

theorem solve_positive_implies_exists_gt (n : Nat) (pairs : List (Nat × Nat)) :
  solve n pairs > 0 → ∃ p ∈ pairs, p.1 > p.2 := sorry

theorem solve_is_total_minus_one_b (n : Nat) (pairs : List (Nat × Nat)) :
  solve n pairs > 0 → 
  ∃ b, b ∈ pairs.map (fun p => p.2) ∧ 
       solve n pairs = pairs.foldl (fun acc p => acc + p.1) 0 - b := sorry

theorem solve_identical_pairs (n : Nat) (val : Nat) :
  let pairs := List.replicate n (val, val)
  solve n pairs = 0 := sorry
-- </vc-theorems>