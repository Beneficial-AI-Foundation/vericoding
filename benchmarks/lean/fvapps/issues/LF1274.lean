-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solveExecutions (citizens : List Int) (visits : Nat) : List Int := sorry

theorem basic_execution_length
  {wealth_values : List Int}
  (h₁ : ∀ x ∈ wealth_values, 1 ≤ x ∧ x ≤ 10000)
  (h₂ : 1 ≤ wealth_values.length ∧ wealth_values.length ≤ 20)
  (h₃ : citizens = [wealth_values[0]!, -1])
  : (solveExecutions citizens 1).length = 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem basic_execution_value
  {wealth_values : List Int}
  (h₁ : ∀ x ∈ wealth_values, 1 ≤ x ∧ x ≤ 10000)
  (h₂ : 1 ≤ wealth_values.length ∧ wealth_values.length ≤ 20)
  (h₃ : citizens = [wealth_values[0]!, -1])
  : (solveExecutions citizens 1)[0]! = wealth_values[0]! := sorry

theorem single_pair_length
  {wealth : Int}
  (h₁ : 1 ≤ wealth ∧ wealth ≤ 10000)
  (h₂ : citizens = [wealth, -1])
  : (solveExecutions citizens 1).length = 1 := sorry

theorem single_pair_value
  {wealth : Int}
  (h₁ : 1 ≤ wealth ∧ wealth ≤ 10000) 
  (h₂ : citizens = [wealth, -1])
  : (solveExecutions citizens 1)[0]! = wealth := sorry
-- </vc-theorems>