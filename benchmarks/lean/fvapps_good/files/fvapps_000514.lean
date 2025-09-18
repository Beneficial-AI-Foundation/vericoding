-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_shots_to_find_x (n: Nat) (l: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_bullet_shots (l: Nat) (h: l > 0):
  min_shots_to_find_x 1 l = l := by
  sorry

theorem two_bullets_shots (l: Nat) (h: l > 0):
  ∃ k, min_shots_to_find_x 2 l = k ∧ k ≥ 1 := by
  sorry

theorem n_bullets_shots (n l: Nat) (hn: n > 2) (hl: l > 0):
  ∃ k, min_shots_to_find_x n l = k ∧ k * (n + 1) ≥ l := by
  sorry

theorem shots_always_positive (n l: Nat) (hn: n > 0) (hl: l > 0):
  min_shots_to_find_x n l > 0 := by
  sorry

theorem shots_less_than_length (n l: Nat) (hn: n > 0) (hl: l > 0):
  min_shots_to_find_x n l ≤ l := by
  sorry
-- </vc-theorems>