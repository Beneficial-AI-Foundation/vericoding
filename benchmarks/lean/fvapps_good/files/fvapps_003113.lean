-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve : String → Nat := sorry

theorem solve_length_bound (s : String) : 
  solve s ≤ (s.length / 2) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_nonnegative (s : String) :
  solve s ≥ 0 := sorry

theorem solve_valid_match (s : String) :
  solve s > 0 → solve s ≤ s.length / 2 ∧ 
  s.take (solve s) = s.takeRight (solve s) := sorry

theorem solve_concatenation {s1 s2 : String} 
  (h1 : s1.length > 0) (h2 : s2.length > 0) :
  solve (s1 ++ s2 ++ s1) ≥ s1.length := sorry

theorem solve_empty : solve "" = 0 := sorry

theorem solve_single (c : Char) :
  solve (String.mk [c]) = 0 := sorry
-- </vc-theorems>