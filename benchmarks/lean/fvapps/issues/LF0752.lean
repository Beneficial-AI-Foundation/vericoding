-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_wrestling_challenge (n m f : Nat) (challengers : List Nat) : Result := sorry

theorem wrestling_challenge_no_none_if_yes {n m f : Nat} {challengers : List Nat} :
  solve_wrestling_challenge n m f challengers = Result.Yes city →
  city ∈ ["Multan", "Fultan", "Both"] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem wrestling_challenge_valid_result {n m f : Nat} {challengers : List Nat} :
  solve_wrestling_challenge n m f challengers = Result.Yes city ∨
  solve_wrestling_challenge n m f challengers = Result.No := sorry

theorem wrestling_challenge_all_zeros {n m f : Nat} : 
  solve_wrestling_challenge n m f (List.replicate n 0) = Result.No := sorry

theorem wrestling_challenge_win_percentage {n m f : Nat} {challengers : List Nat} :
  (challengers.length = n) →
  let wins := (challengers.filter (λ x => x > 0 ∧ (x % m = 0 ∨ x % f = 0))).length
  let win_percentage := (wins * 100) / n
  win_percentage ≥ 70 ↔ ∃ city, solve_wrestling_challenge n m f challengers = Result.Yes city := sorry

/-
info: ('Yes', 'Multan')
-/
-- #guard_msgs in
-- #eval solve_wrestling_challenge 7 2 3 [4, 5, 7, 8, 9, 10, 14]

/-
info: ('No', None)
-/
-- #guard_msgs in
-- #eval solve_wrestling_challenge 6 5 7 [1, 2, 8, 9, 10, 11]
-- </vc-theorems>