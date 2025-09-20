-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_discounted (s : String) : String := sorry

theorem empty_and_whitespace
  (s : String) (h : s.trim = "") :
  find_discounted s = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem specific_case_1 :
  find_discounted "15 20 60 75 80 100" = "15 60 75" := sorry

theorem specific_case_2 :
  find_discounted "9 9 12 12 12 15 16 20" = "9 9 12 15" := sorry

theorem specific_case_3 :
  find_discounted "0 0" = "0" := sorry
-- </vc-theorems>