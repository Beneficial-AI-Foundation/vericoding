-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def are_strings_transformable (s t : String) : Bool := sorry

theorem are_strings_transformable_reflexive (s t : String) 
  (h : s.length > 0 ∧ t.length > 0) :
  are_strings_transformable s t = are_strings_transformable t s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem are_strings_transformable_self (s : String) 
  (h : s.length > 0) : 
  are_strings_transformable s s = true := sorry

theorem no_shared_chars_implies_not_transformable (s t : String)
  (h1 : s.length > 0)
  (h2 : ∀ c, c ∈ s.data → c ∉ t.data) :
  are_strings_transformable s t = false := sorry

theorem shared_chars_implies_transformable (s t : String)
  (h1 : s.length > 0 ∧ t.length > 0)
  (h2 : ∃ c, c ∈ s.data ∧ c ∈ t.data) :
  are_strings_transformable s t = true := sorry
-- </vc-theorems>