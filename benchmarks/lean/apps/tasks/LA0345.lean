-- <vc-preamble>
def ValidInput (cards : List Int) : Prop :=
  cards.length ≥ 1 ∧
  (∀ i, 0 ≤ i ∧ i < cards.length → cards[i]! > 0) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < cards.length → cards[i]! ≠ cards[j]!)

def sum (cards : List Int) : Int :=
  cards.sum

def sereja_optimal_score (cards : List Int) (left : Int) (right : Int) (sereja_turn : Bool) : Int :=
  if h : 0 ≤ left ∧ left ≤ right ∧ right < cards.length then
    if left = right then
      if sereja_turn then cards[left.toNat]! else 0
    else if cards[left.toNat]! > cards[right.toNat]! then
      (if sereja_turn then cards[left.toNat]! else 0) + sereja_optimal_score cards (left+1) right (!sereja_turn)
    else
      (if sereja_turn then cards[right.toNat]! else 0) + sereja_optimal_score cards left (right-1) (!sereja_turn)
  else 0
termination_by (right - left + 1).toNat

def ValidOutput (scores : List Int) (cards : List Int) : Prop :=
  scores.length = 2 ∧
  scores[0]! ≥ 0 ∧ scores[1]! ≥ 0 ∧
  scores[0]! + scores[1]! = sum cards ∧
  scores[0]! = sereja_optimal_score cards 0 (cards.length - 1) true ∧
  scores[1]! = sum cards - sereja_optimal_score cards 0 (cards.length - 1) true

@[reducible, simp]
def solve_precond (cards : List Int) : Prop :=
  ValidInput cards
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (cards : List Int) (h_precond : solve_precond cards) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (cards : List Int) (scores : List Int) (h_precond : solve_precond cards) : Prop :=
  ValidOutput scores cards

theorem solve_spec_satisfied (cards : List Int) (h_precond : solve_precond cards) :
    solve_postcond cards (solve cards h_precond) h_precond := by
  sorry
-- </vc-theorems>