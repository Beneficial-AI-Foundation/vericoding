-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_powers (a b m : Nat) : Nat × Nat := sorry

theorem calculate_powers_mod_less (a b m : Nat) (h : m > 0) : 
  let (_, mod_result) := calculate_powers a b m
  0 ≤ mod_result ∧ mod_result < m := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_powers_result_mod_eq (a b m : Nat) (h : m > 0) : 
  let (_, mod_result) := calculate_powers a b m
  mod_result = (a^b) % m := sorry

theorem calculate_powers_first_result (a b : Nat) (m : Nat) :
  let (result, _) := calculate_powers a b m  
  result = a^b := sorry

theorem calculate_powers_types (a b m : Nat) :
  let result := calculate_powers a b m
  result.1 ≥ 0 ∧ result.2 ≥ 0 := sorry
-- </vc-theorems>