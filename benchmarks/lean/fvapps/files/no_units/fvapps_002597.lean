-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tickets (bills : List Nat) : String := sorry

theorem tickets_valid_output (bills: List Nat) :
  bills.length > 0 → tickets bills = "YES" ∨ tickets bills = "NO" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem first_payment_25 (bills: List Nat) :
  bills.length > 0 → bills[0]! ≠ 25 → tickets bills = "NO" := sorry 

theorem simple_cases_work :
  tickets [25] = "YES" ∧ tickets [25, 25] = "YES" := sorry

theorem successful_case_has_change (bills : List Nat) (i : Nat) :
  i < bills.length →
  tickets bills = "YES" → 
  let payment := bills[i]!
  let prev_bills := List.take i bills
  let till_25 := prev_bills.filter (· == 25) |>.length
  let till_50 := prev_bills.filter (· == 50) |>.length
  till_25 * 25 + till_50 * 50 ≥ payment - 25 := sorry

theorem invalid_bills_error (bills : List Nat) :
  (∃ x ∈ bills, x ≠ 25 ∧ x ≠ 50 ∧ x ≠ 100) →
  tickets bills = "NO" := sorry
-- </vc-theorems>