-- <vc-helpers>
-- </vc-helpers>

def solve (n : Nat) (pairs : List (Nat × Nat)) : Nat := sorry 

theorem solve_non_negative (n : Nat) (pairs : List (Nat × Nat)) :
  solve n pairs ≥ 0 := sorry

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

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve 2 [(1, 2), (3, 2)]

/-
info: 9
-/
-- #guard_msgs in
-- #eval solve 3 [(8, 3), (0, 1), (4, 8)]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve 1 [(1, 1)]

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible