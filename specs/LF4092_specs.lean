-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseByCenter (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverseByCenter_length_preserved (s : String) :
  (reverseByCenter s).length = s.length :=
sorry

theorem reverseByCenter_is_reversible (s : String) :
  reverseByCenter (reverseByCenter s) = s :=
sorry

theorem reverseByCenter_ends_swapped {s : String} (h : s.length ≥ 2) :
  let n := s.length/2
  (reverseByCenter s).take n = s.takeRight n ∧
  (reverseByCenter s).takeRight n = s.take n :=
sorry

theorem reverseByCenter_middle_preserved {s : String} (h : s.length ≥ 3) :
  let n := s.length/2
  (reverseByCenter s).drop n = s.drop n :=
sorry

theorem reverseByCenter_empty :
  reverseByCenter "" = "" :=
sorry
-- </vc-theorems>