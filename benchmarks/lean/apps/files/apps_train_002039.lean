def solve_startups (n : Nat) (arr : List Int) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def pow (base : Nat) (exp : Nat) (m : Nat) : Nat :=
  sorry

theorem result_in_valid_range (n : Nat) (arr : List Int) (h₁ : n > 0) (h₂ : arr.length = n) :
  let result := solve_startups n arr
  0 ≤ result ∧ result < 1000000007 :=
  sorry

theorem array_length_matches_n (n : Nat) (arr : List Int) 
  (h₁ : n > 0) (h₂ : arr.length ≥ 1) :
  let truncated := (List.replicate n arr.head!).take n
  let result := solve_startups n truncated
  0 ≤ result ∧ result < 1000000007 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_startups 3 [-1, -1, -1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_startups 2 [2, -1]

/-
info: 755808950
-/
-- #guard_msgs in
-- #eval solve_startups 40 [3, 3, -1, -1, 4, 4, -1, -1, -1, -1, -1, 10, 10, 10, 10, 10, 10, 4, 20, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 3, 3, 3, 3, 3, 3, 3, 3]

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible