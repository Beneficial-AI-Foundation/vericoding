-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def PokerHand.compare_with (h1 h2 : PokerHand) : String :=
  sorry

/- Comparing hands is symmetric: if h1 beats h2, then h2 loses to h1 -/
-- </vc-definitions>

-- <vc-theorems>
theorem compare_symmetry (h1 h2 : PokerHand) : 
  (h1.compare_with h2 = "Win" → h2.compare_with h1 = "Loss") ∧
  (h1.compare_with h2 = "Loss" → h2.compare_with h1 = "Win") ∧
  (h1.compare_with h2 = "Tie" → h2.compare_with h1 = "Tie") :=
  sorry

/- A hand compared to itself always ties -/

theorem self_comparison_tie (h : PokerHand) :
  h.compare_with h = "Tie" :=
  sorry
-- </vc-theorems>