-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def three_by_n (n : Nat) : Nat := sorry

theorem three_by_n_output_bounds (n : Nat) (h : n > 0) : 
  three_by_n n < 12345787 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem three_by_n_monotonic (n : Nat) (h : n > 0) (h2 : n ≤ 100) :
  three_by_n n ≤ three_by_n (n + 1) ∨ 
  three_by_n (n + 1) % 12345787 < three_by_n n := sorry

theorem three_by_n_base_cases :
  three_by_n 1 = 2 ∧ three_by_n 2 = 3 := sorry

theorem three_by_n_mod (n : Nat) (h : n > 0) :
  three_by_n n = three_by_n n % 12345787 := sorry
-- </vc-theorems>