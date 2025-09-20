-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def titleToNumber (s : String) : Nat := sorry

theorem title_to_number_positive (s : String) (h : s.all (fun c => 'A' ≤ c ∧ c ≤ 'Z')) : 
  titleToNumber s > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem title_to_number_single_char_range (c : Char) (h : 'A' ≤ c ∧ c ≤ 'Z') :
  1 ≤ titleToNumber (String.mk [c]) ∧ titleToNumber (String.mk [c]) ≤ 26 := sorry

theorem title_to_number_recursive (s : String) (c : Char) 
  (h1 : s.all (fun c => 'A' ≤ c ∧ c ≤ 'Z')) 
  (h2 : 'A' ≤ c ∧ c ≤ 'Z') :
  titleToNumber (s.push c) = titleToNumber s * 26 + (c.toNat - 'A'.toNat + 1) := sorry
-- </vc-theorems>