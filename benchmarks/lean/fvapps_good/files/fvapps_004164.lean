-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def men_still_standing (cards: List String) : (Nat × Nat) :=
  sorry

-- Empty input returns initial state
-- </vc-definitions>

-- <vc-theorems>
theorem initial_state :
  men_still_standing [] = (11, 11) :=
sorry

-- Results can only decrease monotonically

theorem monotonic_decrease {cards : List String} {i : Nat} :
  i < cards.length →
  let (a₁, b₁) := men_still_standing (cards.take i)
  let (a₂, b₂) := men_still_standing (cards.take (i+1))
  a₂ ≤ a₁ ∧ b₂ ≤ b₁ :=
sorry

-- When either team goes below 7, adding more cards doesn't change result  

theorem early_termination {cards extra : List String} :
  cards ≠ [] →
  let (a, b) := men_still_standing cards
  (a < 7 ∨ b < 7) →
  men_still_standing (cards ++ extra) = (a, b) :=
sorry

-- Results are always between 0 and 11

theorem valid_range {cards : List String} :
  let (a, b) := men_still_standing cards
  0 ≤ a ∧ a ≤ 11 ∧ 0 ≤ b ∧ b ≤ 11 :=
sorry
-- </vc-theorems>