-- <vc-helpers>
-- </vc-helpers>

def Winner := String

def determine_winner (n : Nat) (k : Nat) (stack : List Nat) (moves : List Nat) : Winner := sorry

theorem winner_is_valid (n : Nat) (k : Nat) (stack : List Nat) (moves : List Nat)
  (hn : n ≥ 1) (hk : k ≥ 1 ∧ k ≤ 10) 
  (hstack : stack.length ≤ n ∧ ∀ x ∈ stack, x ≥ 1)
  (hmoves : moves.length ≤ k ∧ ∀ x ∈ moves, x ≥ 1) :
  determine_winner n k stack moves = "Chef" ∨ 
  determine_winner n k stack moves = "Garry" := sorry

theorem winner_is_deterministic (stack moves : List Nat)
  (hstack : ∀ x ∈ stack, x ≥ 1)
  (hmoves : ∀ x ∈ moves, x ≥ 1) :
  determine_winner stack.length moves.length stack moves = 
  determine_winner stack.length moves.length stack moves := sorry

/-
info: 'Chef'
-/
-- #guard_msgs in
-- #eval determine_winner 3 2 [5, 7, 1] [1, 2]

/-
info: 'Chef'
-/
-- #guard_msgs in
-- #eval determine_winner 4 2 [1, 2, 3, 4] [1, 2]

/-
info: 'Garry'
-/
-- #guard_msgs in
-- #eval determine_winner 2 1 [1, 2] [1]

-- Apps difficulty: interview
-- Assurance level: unguarded