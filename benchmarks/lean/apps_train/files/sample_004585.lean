/-
Quite recently it happened to me to join some recruitment interview, where my first task was to write own implementation of built-in split function. It's quite simple, is it not?

However, there were the following conditions:

* the function **cannot** use, in any way, the original `split` or `rsplit` functions,
* the new function **must** be a generator,
* it should behave as the built-in `split`, so it will be tested that way -- think of `split()` and `split('')`

*This Kata will control if the new function is a generator and if it's not using the built-in split method, so you may try to hack it, but let me know if with success, or if something would go wrong!*

Enjoy!
-/

-- <vc-helpers>
-- </vc-helpers>

def my_very_own_split (s : String) (delimiter : String) : List String :=
  sorry

theorem split_matches_python_split (s : String) (delimiter : String) 
  (h : delimiter.length > 0) :
  my_very_own_split s delimiter = s.splitOn delimiter := 
  sorry

theorem split_empty_delimiter_raises (s : String) :
  delimiter.length = 0 → my_very_own_split s delimiter = [] := 
  sorry

theorem split_parts_recombine (s delimiter : String) 
  (h : delimiter.length > 0) 
  (parts := my_very_own_split s delimiter)
  (h2 : parts.length > 1) :
  String.intercalate delimiter parts = s :=
  sorry

theorem split_no_empty_middle_parts (s delimiter : String)
  (h : delimiter.length > 0) 
  (parts := my_very_own_split s delimiter)
  (middle_parts := parts.drop 1 |>.take (parts.length - 2)) :
  ∀ p ∈ middle_parts, p ≠ "" := 
  sorry

-- Apps difficulty: introductory
-- Assurance level: guarded