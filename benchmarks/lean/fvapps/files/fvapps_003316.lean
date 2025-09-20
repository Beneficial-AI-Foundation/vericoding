-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s1 s2 : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nonmatching_returns_zero {s1 s2 : String} (h1 : s1.length > 0) (h2 : s2.length > 0) 
  (h3 : ∃ c ∈ s2.data, c ∉ s1.data) : solve s1 s2 = 0 :=
  sorry 

theorem identical_strings_returns_zero {s : String} (h : s.length > 0) :
  solve s s = 0 :=
  sorry

theorem result_is_nonnegative {s1 s2 : String} (h1 : s1.length > 0) (h2 : s2.length > 0) :
  solve s1 s2 ≥ 0 :=
  sorry

theorem empty_second_string {s : String} (h : s.length > 0) :
  solve s "" = s.length :=
  sorry
-- </vc-theorems>