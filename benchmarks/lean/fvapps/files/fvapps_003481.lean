-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_mult10_SF (n : Nat) : Nat := sorry 

theorem find_mult10_SF_is_multiple_of_10 (n : Nat) 
  (h : 1 ≤ n ∧ n ≤ 10) : 
  find_mult10_SF n % 10 = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_mult10_SF_strictly_increasing (n : Nat)  
  (h : 1 < n ∧ n ≤ 10) :
  find_mult10_SF n > find_mult10_SF (n-1) := sorry

theorem find_mult10_SF_positive (n : Nat)
  (h : 1 ≤ n ∧ n ≤ 10) :
  find_mult10_SF n > 0 := sorry

theorem find_mult10_SF_first_value :
  find_mult10_SF 1 = 60 := sorry
-- </vc-theorems>