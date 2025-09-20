-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def penaltyShots (shots: Nat) (scores: List Nat) : Nat :=
sorry

def abs (n: Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem penalty_shots_score_range {shots score1 score2: Nat}
  (h1: score1 ≤ shots) (h2: score2 ≤ shots)
  (h3: shots ≤ 20) (h4: score1 ≤ 20) (h5: score2 ≤ 20)
  (h6: abs (Int.subNatNat score1 score2) ≤ (if shots > 4 then 2 else 5 - shots + 1)) :
  let result := penaltyShots shots [score1, score2]
  0 ≤ result ∧ result ≤ (if shots > 4 then 2 else 5 - shots + 1) :=
sorry

theorem penalty_shots_sudden_death {shots score1 score2: Nat}
  (h1: shots > 4) (h2: score1 ≤ shots) (h3: score2 ≤ shots)
  (h4: abs (Int.subNatNat score1 score2) ≤ 2) :
  let result := penaltyShots shots [score1, score2]
  0 ≤ result ∧ result ≤ 2 :=
sorry

theorem penalty_shots_regular_rounds {shots score1 score2: Nat}
  (h1: shots ≤ 4) (h2: score1 ≤ shots) (h3: score2 ≤ shots)
  (h4: abs (Int.subNatNat score1 score2) ≤ (5 - shots + 1)) :
  let result := penaltyShots shots [score1, score2]
  0 ≤ result ∧ result ≤ (5 - shots + 1) :=
sorry
-- </vc-theorems>