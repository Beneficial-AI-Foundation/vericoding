-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_net_income (income : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem net_income_leq_gross (income : Int) : 
  income ≥ 0 → 
  (if income > 250000 then calculate_net_income income ≤ income 
   else calculate_net_income income = income) :=
sorry

theorem net_income_non_negative (income : Int) :
  income ≥ 0 →
  calculate_net_income income ≥ 0 :=
sorry

theorem tax_brackets (income : Int) :
  income ≥ 0 →
  (income ≤ 250000 → calculate_net_income income = income) ∧
  (250000 < income ∧ income ≤ 500000 → 
    calculate_net_income income ≥ income - (income - 250000) / 20 - 1) ∧
  (500000 < income ∧ income ≤ 750000 →
    calculate_net_income income ≥ income - (income - 500000) / 10 - 25000 - 1) ∧
  (750000 < income ∧ income ≤ 1000000 →
    calculate_net_income income ≥ income - (income - 750000) * 3 / 20 - 50000 - 1) ∧
  (1000000 < income ∧ income ≤ 1250000 →
    calculate_net_income income ≥ income - (income - 1000000) / 5 - 87500 - 1) ∧
  (1250000 < income ∧ income ≤ 1500000 →
    calculate_net_income income ≥ income - (income - 1250000) / 4 - 137500 - 1) ∧
  (income > 1500000 →
    calculate_net_income income ≥ income - (income - 1500000) * 3 / 10 - 200000 - 1) :=
sorry
-- </vc-theorems>