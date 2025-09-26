-- <vc-preamble>
@[reducible, simp]
def smallestMissingNumber_precond (s : Array Int) :=
  (∀ i j, 0 ≤ i → i < j → j < s.size → s[i]! ≤ s[j]!) ∧ 
  (∀ i, 0 ≤ i → i < s.size → s[i]! ≥ 0) ∧ 
  s.size ≤ 100000
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def smallestMissingNumber (s : Array Int) (h_precond : smallestMissingNumber_precond s) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def smallestMissingNumber_postcond (s : Array Int) (v : Int) (h_precond : smallestMissingNumber_precond s) :=
  0 ≤ v ∧ 
  (∀ i, 0 ≤ i → i < s.size → s[i]! ≠ v) ∧ 
  (∀ k, 0 ≤ k → k < v → ∃ j, 0 ≤ j ∧ j < s.size ∧ s[j]! = k)

theorem smallestMissingNumber_spec_satisfied (s : Array Int) (h_precond : smallestMissingNumber_precond s) :
    smallestMissingNumber_postcond s (smallestMissingNumber s h_precond) h_precond := by
  sorry
-- </vc-theorems>