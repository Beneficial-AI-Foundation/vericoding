-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def value_at (poly: List Int) (x: Float) : Float :=
sorry

def aCb (a: Float) (b: Int) : Float :=
sorry

def intToFloat (i: Int) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem value_at_results_finite (poly: List Int) (x: Float) (h1: poly.length > 0)
  (h2: -10 ≤ x ∧ x ≤ 10) : ∃ (y: Float), value_at poly x = y :=
sorry

theorem aCb_matches_binomial (a b: Int) (h1: 0 ≤ a ∧ a ≤ 10) (h2: 0 ≤ b ∧ b ≤ 10)
  (h3: b ≤ a) : ∃ (y: Float), aCb (intToFloat a) b = y :=
sorry

theorem aCb_results_finite (a: Float) (b: Int) (h1: -10 ≤ a ∧ a ≤ 10)
  (h2: 0 ≤ b ∧ b ≤ 5) : ∃ (y: Float), aCb a b = y :=
sorry

theorem value_at_constant (c: Int) (h1: -10 ≤ c ∧ c ≤ 10) :
  (value_at [c] 123 - intToFloat c) < 0.01 ∧ (intToFloat c - value_at [c] 123) < 0.01 :=
sorry
-- </vc-theorems>