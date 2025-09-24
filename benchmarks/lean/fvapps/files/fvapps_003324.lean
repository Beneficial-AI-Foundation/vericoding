-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dig_pow (n : Nat) : Nat := sorry

def sum_dig_pow (a b : Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dig_pow_nonnegative (n : Nat) : 
  0 ≤ dig_pow n := sorry

theorem dig_pow_is_nat (n : Nat) : 
  dig_pow n = dig_pow n := sorry

theorem sum_dig_pow_elements_in_range (a b : Nat) (h : a ≤ b) :
  ∀ x ∈ sum_dig_pow a b, a ≤ x ∧ x ≤ b := sorry

theorem sum_dig_pow_all_satisfy_dig_pow (a b : Nat) (h : a ≤ b) :
  ∀ x ∈ sum_dig_pow a b, dig_pow x = x := sorry

theorem sum_dig_pow_sorted (a b : Nat) (h : a ≤ b) :
  ∀ i j, i < j → j < (sum_dig_pow a b).length → 
  (sum_dig_pow a b).get ⟨i, sorry⟩ ≤ (sum_dig_pow a b).get ⟨j, sorry⟩ := sorry

theorem sum_dig_pow_single (n : Nat) :
  sum_dig_pow n n = if dig_pow n = n then [n] else [] := sorry
-- </vc-theorems>