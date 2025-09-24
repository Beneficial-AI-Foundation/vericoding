-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def points (dice: String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem points_valid_score (dice: String) (h: dice.length = 5) 
  (h': ∀ c ∈ dice.data, '1' ≤ c ∧ c ≤ '6') :
  points dice = 0 ∨ points dice = 20 ∨ points dice = 30 ∨ points dice = 40 ∨ points dice = 50 := 
sorry

theorem generala_iff (dice: String) (h: dice.length = 5) 
  (h': ∀ c ∈ dice.data, '1' ≤ c ∧ c ≤ '6') :
  (∀ (c₁ c₂ : Char), c₁ ∈ dice.data → c₂ ∈ dice.data → c₁ = c₂) ↔ 
  points dice = 50 :=
sorry

theorem poker_iff (dice: String) (h: dice.length = 5)
  (h': ∀ c ∈ dice.data, '1' ≤ c ∧ c ≤ '6') :
  (∃ d, (dice.data.filter (· = d)).length ≥ 4) ↔
  points dice = 40 :=
sorry

theorem full_house_score (dice: String) (h: dice.length = 5)
  (h': ∀ c ∈ dice.data, '1' ≤ c ∧ c ≤ '6') :
  points dice = 30 →
  ∃ d₁ d₂, d₁ ≠ d₂ ∧
    (dice.data.filter (· = d₁)).length = 3 ∧
    (dice.data.filter (· = d₂)).length = 2 :=
sorry

theorem points_permutation_invariant (dice₁ dice₂: String) 
  (h₁: dice₁.length = 5) (h₂: dice₂.length = 5)
  (h₁': ∀ c ∈ dice₁.data, '1' ≤ c ∧ c ≤ '6')
  (h₂': ∀ c ∈ dice₂.data, '1' ≤ c ∧ c ≤ '6')
  (h: ∀ c, (dice₁.data.filter (· = c)).length = (dice₂.data.filter (· = c)).length) :
  points dice₁ = points dice₂ :=
sorry
-- </vc-theorems>