-- <vc-preamble>
def sum (cards: List Int): Int :=
  cards.foldr (· + ·) 0

def abs (x: Int): Int :=
  if x ≥ 0 then x else -x

def ValidInput (cards: List Int) (x: Int): Prop :=
  x > 0 ∧ cards.length ≥ 1 ∧ ∀ i, 0 ≤ i ∧ i < cards.length → -x ≤ cards[i]! ∧ cards[i]! ≤ x

@[reducible, simp]
def solve_precond (cards: List Int) (x: Int) : Prop :=
  ValidInput cards x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (cards: List Int) (x: Int) (h_precond : solve_precond cards x) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (cards: List Int) (x: Int) (result: Int) (h_precond : solve_precond cards x) : Prop :=
  result ≥ 0 ∧ result = if sum cards = 0 then 0 else (abs (sum cards) + x - 1) / x

theorem solve_spec_satisfied (cards: List Int) (x: Int) (h_precond : solve_precond cards x) :
    solve_postcond cards x (solve cards x h_precond) h_precond := by
  sorry
-- </vc-theorems>