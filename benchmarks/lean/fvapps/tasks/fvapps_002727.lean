-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution (s : String) : String := sorry 

theorem solution_reverse_involution (s : String) : 
  solution (solution s) = s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_length_preserved (s : String) :
  (solution s).length = s.length := sorry

theorem solution_chars_preserved (s : String) : ∀ c,
  (s.data.count c) = ((solution s).data.count c) := sorry

theorem solution_eq_reverse (s : String) :
  solution s = String.mk s.data.reverse := sorry

theorem solution_empty : 
  solution "" = "" := sorry
-- </vc-theorems>