/-
# Write Number in Expanded Form - Part 2

This is version 2 of my ['Write Number in Exanded Form' Kata](https://www.codewars.com/kata/write-number-in-expanded-form).

You will be given a number and you will need to return it as a string in [Expanded Form](https://www.mathplacementreview.com/arithmetic/decimals.php#writing-a-decimal-in-expanded-form). For example:

```python
expanded_form(1.24) # Should return '1 + 2/10 + 4/100'
expanded_form(7.304) # Should return '7 + 3/10 + 4/1000'
expanded_form(0.04) # Should return '4/100'
```
-/

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