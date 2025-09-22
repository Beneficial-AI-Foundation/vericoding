-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sc_perm_comb (n : Nat) : Nat := sorry

theorem sc_perm_comb_non_negative (n : Nat) :
  sc_perm_comb n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sc_perm_comb_geq_input (n : Nat) :
  sc_perm_comb n ≥ n := sorry 

theorem sc_perm_comb_single_digit (n : Nat) (h : n ≤ 9) :
  sc_perm_comb n = n := sorry

theorem sc_perm_comb_zero :
  sc_perm_comb 0 = 0 := sorry

theorem sc_perm_comb_two_digits (n : Nat) (h1 : n ≥ 10) (h2 : n ≤ 99) 
    (h3 : n % 10 ≠ n / 10) :
  sc_perm_comb n ≥ n + (n % 10 * 10 + n / 10) := sorry
-- </vc-theorems>