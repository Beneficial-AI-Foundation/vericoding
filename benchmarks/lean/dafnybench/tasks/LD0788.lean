-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MinPair (s : Array Int) : Int :=
sorry

def min (s : Array Int) : Int :=
sorry

def SecondSmallest (s : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem MinPair_spec (s : Array Int) :
s.size = 2 →
((s[0]! ≤ s[1]!) → MinPair s = s[0]!) ∧
((s[0]! > s[1]!) → MinPair s = s[1]!) :=
sorry

theorem min_spec (s : Array Int) :
s.size ≥ 2 →
∀ i, 0 ≤ i ∧ i < s.size → min s ≤ s[i]! :=
sorry

theorem SecondSmallest_spec (s : Array Int) (result : Int) :
s.size ≥ 2 →
(∃ i j, 0 ≤ i ∧ i < s.size ∧ 0 ≤ j ∧ j < s.size ∧ i ≠ j ∧ s[i]! = min s ∧ s[j]! ≠ s[i]!) →
(∃ i j, 0 ≤ i ∧ i < s.size ∧ 0 ≤ j ∧ j < s.size ∧ i ≠ j ∧ s[i]! = min s ∧ s[j]! = result) ∧
(∀ k, 0 ≤ k ∧ k < s.size ∧ s[k]! ≠ min s → s[k]! ≥ result) :=
sorry
-- </vc-theorems>