-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_states_won (A B : Nat) (c_votes d_votes : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_states_won_bounded {A B : Nat} {c_votes d_votes : List Nat}
  (h1 : 0 < A) (h2 : 0 < B)
  (h3 : c_votes.length = A * B) (h4 : d_votes.length = A * B) :
  0 ≤ max_states_won A B c_votes d_votes ∧ max_states_won A B c_votes d_votes ≤ A :=
sorry

theorem max_states_won_zero_votes {A B : Nat} {d_votes : List Nat}
  (h1 : 0 < A) (h2 : 0 < B)
  (h3 : d_votes.length = A * B) :
  max_states_won A B (List.replicate (A*B) 0) d_votes = 0 :=
sorry

theorem max_states_won_dominant_votes {A B : Nat} {d_votes : List Nat}
  (h1 : 0 < A) (h2 : 0 < B)
  (h3 : d_votes.length = A * B) :
  let max_d := d_votes.foldl Nat.max 0
  let dominant_votes := List.replicate (A*B) (max_d + 1)
  max_states_won A B dominant_votes d_votes = A :=
sorry

theorem max_states_won_empty {A B : Nat}
  (h1 : 0 < A) (h2 : 0 < B) :
  max_states_won A B (List.replicate (A*B) 0) (List.replicate (A*B) 0) = 0 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval max_states_won 1 3 [4, 2, 9] [5, 6, 7]

/-
info: 0
-/
-- #guard_msgs in
-- #eval max_states_won 1 3 [4, 2, 9] [5, 10, 7]

/-
info: 3
-/
-- #guard_msgs in
-- #eval max_states_won 3 3 [7, 14, 11, 4, 15, 5, 20, 1, 17] [2, 13, 16, 9, 19, 6, 12, 8, 10]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible