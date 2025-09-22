-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def S2N (m n : Nat) : Nat := sorry

theorem s2n_nonnegative (m n : Nat) : 
  m ≤ 20 → n ≤ 10 → S2N m n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem s2n_increasing_n (m n : Nat) :
  m ≤ 10 → n ≤ 5 → n > 0 → S2N m n ≥ S2N m (n-1) := sorry

theorem s2n_increasing_m (m n : Nat) :
  m ≤ 10 → n ≤ 5 → m > 0 → S2N m n ≥ S2N (m-1) n := sorry

theorem s2n_base_cases :
  (S2N 0 0 = 1) ∧ (S2N 1 0 = 2) ∧ (S2N 0 1 = 1) := sorry
-- </vc-theorems>