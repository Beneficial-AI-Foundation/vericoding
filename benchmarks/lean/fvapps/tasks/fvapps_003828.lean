-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def substring_test (s1 s2 : String) : Bool := sorry

theorem substring_test_case_insensitive (s1 s2 : String) :
  substring_test s1.toUpper s2.toLower = substring_test s1 s2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem substring_test_contains_exact (s1 s2 : String) :
  s1.length ≥ 2 →
  substring_test s1 (s2 ++ s1.take 2) = true := sorry

theorem substring_test_empty_or_single (s1 s2 : String) :
  (s1.length ≤ 1 ∨ s2.length ≤ 1) →
  substring_test s1 s2 = false := sorry

theorem substring_test_symmetric (s1 s2 : String) :
  s1.length > 1 →
  s2.length > 1 →
  substring_test s1 s2 = substring_test s2 s1 := sorry
-- </vc-theorems>