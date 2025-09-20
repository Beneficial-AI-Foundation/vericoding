-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_strings_equal (s1 s2 target : String) : Bool := sorry

theorem identical_strings {s : String} (h : s.length > 0) : 
  can_strings_equal s s s = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem matching_lengths {s1 s2 : String} 
  (h1 : s1.length > 0) (h2 : s2.length > 0) 
  (h3 : s1.length = s2.length) :
  can_strings_equal s1 s2 s1 = true := sorry

theorem argument_order {s1 s2 : String}
  (h1 : s1.length > 0) (h2 : s2.length > 0)
  (h3 : s1.length = s2.length) :
  can_strings_equal s1 s2 s1 = can_strings_equal s2 s1 s1 := sorry
-- </vc-theorems>