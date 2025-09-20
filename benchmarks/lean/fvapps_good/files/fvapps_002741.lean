-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def seven (n : Nat) : Nat × Nat := sorry

theorem seven_returns_pair (n : Nat) :
  ∃ (res num : Nat), seven n = (res, num) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem seven_step_count_non_negative (n : Nat) :
  (seven n).2 ≥ 0 := sorry

theorem seven_result_below_100 (n : Nat) :
  (seven n).1 < 100 := sorry

theorem seven_smaller_inputs (n : Nat) : 
  n < 100 → (seven n).2 = 0 ∧ (seven n).1 = n := sorry

theorem seven_order_invariant (n1 n2 : Nat) :
  (seven n1).1 = (seven n2).1 → 
    (n1 ≤ n2 → (seven n1).2 ≤ (seven n2).2) ∧
    (n1 ≥ n2 → (seven n1).2 ≥ (seven n2).2) := sorry
-- </vc-theorems>