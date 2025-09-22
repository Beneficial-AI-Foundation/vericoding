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
-- </vc-helpers>

-- <vc-definitions>
def solve (A B C : String) (h_precond : solve_precond A B C) : Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B C : String) (result : Char) (h_precond : solve_precond A B C) : Prop :=
  ValidWinner result

theorem solve_spec_satisfied (A B C : String) (h_precond : solve_precond A B C) :
    solve_postcond A B C (solve A B C h_precond) h_precond := by
  sorry
-- </vc-theorems>