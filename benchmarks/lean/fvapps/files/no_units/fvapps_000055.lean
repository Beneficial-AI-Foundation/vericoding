-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_equal_sticks (n : Nat) : Nat := sorry

theorem max_equal_sticks_positive (n : Nat) (h : n ≥ 1) : 
  let result := max_equal_sticks n
  result = (n + 1) / 2 ∧ result ≤ n ∧ result ≥ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_equal_sticks_monotonic (n : Nat) (h : n ≥ 1) :
  max_equal_sticks n ≤ max_equal_sticks (n + 1) := sorry
-- </vc-theorems>