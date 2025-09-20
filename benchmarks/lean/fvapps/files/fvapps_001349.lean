-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_array_sum (n l h : Nat) : Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_bounds {n l h : Nat} (hn : n > 0) (hl : l > 0) (hlh : h ≥ l) (hhn : h ≤ n) :
  let (min_sum, max_sum) := solve_array_sum n l h
  min_sum ≤ max_sum ∧ min_sum > 0 ∧ max_sum > 0
  := sorry

theorem min_max_constraints {n l h : Nat} (hn : n > 0) (hl : l > 0) (hlh : h ≥ l) (hhn : h ≤ n) :
  let (min_sum, max_sum) := solve_array_sum n l h
  min_sum ≥ n ∧ max_sum ≤ 2^h * n
  := sorry

theorem boundary_case {n l : Nat} (hn : n > 0) (hl : l > 0) (hln : l ≤ n) :
  let (min_sum, max_sum) := solve_array_sum n l l
  let (alt_min, alt_max) := solve_array_sum n l (l+1)
  alt_max - alt_min ≥ max_sum - min_sum
  := sorry
-- </vc-theorems>