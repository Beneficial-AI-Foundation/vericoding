-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def f (n : Nat) : Nat := sorry
def m (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem f_non_negative (n : Nat) : f n ≥ 0 := sorry

theorem m_non_negative (n : Nat) : m n ≥ 0 := sorry

theorem f_less_than_input (n : Nat) : n > 0 → f n ≤ n := sorry

theorem m_less_than_input (n : Nat) : n > 0 → m n ≤ n := sorry

theorem f_base_case : f 0 = 1 := sorry

theorem m_base_case : m 0 = 0 := sorry
-- </vc-theorems>