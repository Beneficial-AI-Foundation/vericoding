import Mathlib
-- <vc-preamble>
def ValidDeck (deck : String) : Prop :=
  ∀ i, 0 ≤ i ∧ i < deck.length → (deck.data.get! i = 'a' ∨ deck.data.get! i = 'b' ∨ deck.data.get! i = 'c')

def ValidInput (A B C : String) : Prop :=
  ValidDeck A ∧ ValidDeck B ∧ ValidDeck C

def ValidWinner (winner : Char) : Prop :=
  winner = 'A' ∨ winner = 'B' ∨ winner = 'C'

@[reducible, simp]
def solve_precond (A B C : String) : Prop :=
  ValidInput A B C
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def winner_by_length_rule (lenA lenB lenC : Nat) : Char := 
  if lenA ≥ lenB then
    if lenA ≥ lenC then
      'A'
    else
      'C'
  else
    if lenB ≥ lenC then
      'B'
    else
      'C'

-- LLM HELPER
theorem winner_by_length_rule_is_valid (lenA lenB lenC : Nat) :
    ValidWinner (winner_by_length_rule lenA lenB lenC) := by
  unfold winner_by_length_rule ValidWinner
  split_ifs <;> simp

-- </vc-helpers>

-- <vc-definitions>
def solve (A B C : String) (h_precond : solve_precond A B C) : Char :=
  winner_by_length_rule A.length B.length C.length
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B C : String) (result : Char) (h_precond : solve_precond A B C) : Prop :=
  ValidWinner result

theorem solve_spec_satisfied (A B C : String) (h_precond : solve_precond A B C) :
    solve_postcond A B C (solve A B C h_precond) h_precond := by
  simp [solve, solve_postcond]
  apply winner_by_length_rule_is_valid
-- </vc-theorems>
