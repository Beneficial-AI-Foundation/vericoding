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
-- LLM HELPER: Calculate score of a deck based on card values
def deckScore (deck : String) : Nat :=
  deck.data.foldl (fun acc c => acc + match c with
    | 'a' => 1
    | 'b' => 2
    | 'c' => 3
    | _ => 0) 0

-- LLM HELPER: Determine winner based on deck scores with tiebreaker A > B > C
def determineWinner (scoreA scoreB scoreC : Nat) : Char :=
  if scoreA ≥ scoreB ∧ scoreA ≥ scoreC then 'A'
  else if scoreB ≥ scoreC then 'B'
  else 'C'
-- </vc-helpers>

-- <vc-definitions>
def solve (A B C : String) (h_precond : solve_precond A B C) : Char :=
  let scoreA := deckScore A
  let scoreB := deckScore B
  let scoreC := deckScore C
  determineWinner scoreA scoreB scoreC
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B C : String) (result : Char) (h_precond : solve_precond A B C) : Prop :=
  ValidWinner result

theorem solve_spec_satisfied (A B C : String) (h_precond : solve_precond A B C) :
    solve_postcond A B C (solve A B C h_precond) h_precond := by
  unfold solve solve_postcond ValidWinner determineWinner
  simp only []
  -- The goal is to show the result is 'A', 'B', or 'C'
  -- Since determineWinner always returns one of these three values
  by_cases h1 : deckScore A ≥ deckScore B ∧ deckScore A ≥ deckScore C
  · simp [h1]
  · by_cases h2 : deckScore B ≥ deckScore C
    · simp [h1, h2]
    · simp [h1, h2]
-- </vc-theorems>
