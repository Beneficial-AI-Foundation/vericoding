-- <vc-helpers>
-- </vc-helpers>

def solve_kingdom (n : Nat) (roads : List (Nat × Nat)) (plans : List (Nat × List Nat)) : List Int :=
sorry

theorem solve_kingdom_result_length {n : Nat} {roads : List (Nat × Nat)} {plans : List (Nat × List Nat)} :
  List.length (solve_kingdom n roads plans) = List.length plans :=
sorry

theorem solve_kingdom_result_valid_values {n : Nat} {roads : List (Nat × Nat)} {plans : List (Nat × List Nat)} :
  ∀ r ∈ solve_kingdom n roads plans, r = -1 ∨ r ≥ 0 :=
sorry 

theorem solve_kingdom_result_bounded {n : Nat} {roads : List (Nat × Nat)} {plans : List (Nat × List Nat)} :
  ∀ r ∈ solve_kingdom n roads plans, r = -1 ∨ r ≤ n :=
sorry

/-
info: [1, -1, 1, -1]
-/
-- #guard_msgs in
-- #eval solve_kingdom 4 [(1, 3), (2, 3), (4, 3)] [(2, [1, 2]), (3, [2, 3, 4]), (3, [1, 2, 4]), (4, [1, 2, 3, 4])]

/-
info: [2]
-/
-- #guard_msgs in
-- #eval solve_kingdom 7 [(1, 2), (2, 3), (3, 4), (1, 5), (5, 6), (5, 7)] [(4, [2, 4, 6, 7])]

-- Apps difficulty: competition
-- Assurance level: unguarded