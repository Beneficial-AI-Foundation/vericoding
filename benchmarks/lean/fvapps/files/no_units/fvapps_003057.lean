-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def movie (card : Float) (ticket : Float) (perc : Float) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem movie_returns_positive : 
  ∀ (card ticket perc : Float),
  0 ≤ card → card ≤ 1000 →
  0.1 ≤ ticket → ticket ≤ 100 →
  0.1 ≤ perc → perc ≤ 0.99 →
  movie card ticket perc > 0
  := by sorry

theorem higher_card_more_visits :
  ∀ (card1 card2 ticket perc : Float),
  0 ≤ card1 → card1 ≤ 500 →
  501 ≤ card2 → card2 ≤ 1000 →  
  0.1 ≤ ticket → ticket ≤ 100 →
  0.1 ≤ perc → perc ≤ 0.99 →
  movie card1 ticket perc ≤ movie card2 ticket perc
  := by sorry
-- </vc-theorems>