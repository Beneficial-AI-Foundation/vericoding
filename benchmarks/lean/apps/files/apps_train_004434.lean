-- <vc-helpers>
-- </vc-helpers>

def expanded_form (x : Float) : String := sorry

theorem expanded_form_basic_test_1 : 
  expanded_form 1.24 = "1 + 2/10 + 4/100" := sorry

theorem expanded_form_basic_test_2 :
  expanded_form 7.304 = "7 + 3/10 + 4/1000" := sorry

theorem expanded_form_decimal_only :
  expanded_form 0.04 = "4/100" := sorry

theorem expanded_form_trailing_zeros_1 :
  expanded_form 2.1 = "2 + 1/10" := sorry

theorem expanded_form_trailing_zeros_2 :
  expanded_form 0.001 = "1/1000" := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible