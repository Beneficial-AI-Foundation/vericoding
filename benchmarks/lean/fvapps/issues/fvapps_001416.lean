-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def guessing_game (hints : List Hint) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lies_bounds {hints : List Hint} : 
  let lies := guessing_game hints
  0 ≤ lies ∧ lies ≤ hints.length := by
  sorry

theorem single_hint_result {hint : Hint} :
  let lies := guessing_game [hint]
  lies = 0 ∨ lies = 1 := by
  sorry

theorem contradictory_equal_hints {n m : Nat} (h : n ≠ m) :
  let hints := [⟨'=', n, true⟩, ⟨'=', m, true⟩]
  guessing_game hints = 1 := by
  sorry

theorem opposite_operators_same_number {n : Nat} :
  let hints := [⟨'>', n, true⟩, ⟨'<', n, true⟩]
  guessing_game hints = 1 := by
  sorry

theorem equal_consistency {n : Nat} :
  let hints := [⟨'=', n, true⟩, ⟨'=', n, true⟩]
  guessing_game hints = 0 := by
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval guessing_game [["<", "100", "No"], [">", "100", "No"]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval guessing_game [["<", "2", "Yes"], [">", "4", "Yes"], ["=", "3", "No"]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval guessing_game [["<", "2", "Yes"], [">", "1", "Yes"], ["=", "1", "Yes"], ["=", "1", "Yes"], [">", "1", "Yes"], ["=", "1", "Yes"]]
-- </vc-theorems>