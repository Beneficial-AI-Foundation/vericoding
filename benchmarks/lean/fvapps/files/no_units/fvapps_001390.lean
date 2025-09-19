-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Winner := String

def determine_winner (n : Nat) (k : Nat) (stack : List Nat) (moves : List Nat) : Winner := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>