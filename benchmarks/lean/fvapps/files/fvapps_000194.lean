-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def equal_substring (s t : String) (max_cost : Nat) : Nat := sorry

theorem equal_substring_bounds {s t : String} {max_cost : Nat} 
  (h : s.length = t.length) :
  0 ≤ equal_substring s t max_cost ∧ equal_substring s t max_cost ≤ s.length :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem equal_substring_monotone {s t : String} {max_cost : Nat} 
  (h : s.length = t.length) (h_pos : max_cost > 0) :
  equal_substring s t (max_cost - 1) ≤ equal_substring s t max_cost :=
sorry
-- </vc-theorems>