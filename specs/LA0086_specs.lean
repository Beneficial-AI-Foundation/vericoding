-- <vc-preamble>
def ValidInput (cards : List Int) : Prop :=
  cards.length = 5 ∧ ∀ i, 0 ≤ i ∧ i < cards.length → cards[i]! > 0

def sum (cards : List Int) : Int :=
  cards.foldl (· + ·) 0

def minPossibleSumUpToIndex (cards : List Int) (n : Nat) : Int :=
  0

def minPossibleSum (cards : List Int) (h : ValidInput cards) : Int :=
  minPossibleSumUpToIndex cards 5

@[reducible, simp]
def solve_precond (cards : List Int) : Prop :=
  ValidInput cards
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (cards : List Int) (h_precond : solve_precond cards) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (cards : List Int) (result : Int) (h_precond : solve_precond cards) : Prop :=
  result ≥ 0 ∧ result ≤ sum cards ∧ result = minPossibleSum cards h_precond

theorem solve_spec_satisfied (cards : List Int) (h_precond : solve_precond cards) :
    solve_postcond cards (solve cards h_precond) h_precond := by
  sorry
-- </vc-theorems>