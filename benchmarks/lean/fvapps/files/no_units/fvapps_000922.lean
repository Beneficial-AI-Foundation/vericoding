-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_next_repetition_free (n : Nat) : Nat := sorry

theorem find_next_repetition_free_properties {n : Nat} (h : n > 0 ∧ n ≤ 10000) :
  let result := find_next_repetition_free n
  -- Result is greater than input
  result > n ∧ 
  -- Result has all distinct digits (no repetitions)
  ((toString result).data.eraseDups = (toString result).data) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_next_repetition_free_above_max {n : Nat} (h : n ≥ 987654321) :
  find_next_repetition_free n = 0 := sorry
-- </vc-theorems>