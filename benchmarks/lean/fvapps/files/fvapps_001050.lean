-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_ops_to_zeros (s : String) : Nat := sorry

theorem output_bounds (s : String) :
  let result := min_ops_to_zeros s
  0 ≤ result ∧ result ≤ s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string :
  min_ops_to_zeros "" = 0 := sorry
-- </vc-theorems>