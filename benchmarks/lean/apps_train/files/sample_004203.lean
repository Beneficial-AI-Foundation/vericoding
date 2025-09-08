/-
You need to write a function, that returns the first non-repeated character in the given string.

For example for string `"test"` function should return `'e'`.  
For string `"teeter"` function should return `'r'`.  

If a string contains all unique characters, then return just the first character of the string.  
Example: for input `"trend"` function should return `'t'`  

You can assume, that the input string has always non-zero length.

If there is no repeating character, return `null` in JS or Java, and `None` in Python.
-/

-- <vc-helpers>
-- </vc-helpers>

def first_non_repeated (s : String) : Option Char := sorry

theorem first_non_repeated_all_repeated (s : String) :
  first_non_repeated (s ++ s) = none := sorry

theorem first_non_repeated_single_unique (s : String) (h : s.length > 0) 
  (unique : Char) (h2 : ∀ c ∈ s.data, c ≠ unique) :
  first_non_repeated (s ++ s ++ toString unique ++ s ++ s) = some unique := sorry

theorem first_non_repeated_empty :
  first_non_repeated "" = none := sorry

theorem first_non_repeated_count_one {s : String} {c : Char} 
  (h : first_non_repeated s = some c) :
  (s.data.count c = 1) ∧ 
  (c ∈ s.data) ∧
  (∀ i : Nat, i < s.data.indexOf c → s.data[i]?.map (fun x => s.data.count x) ≠ some 1) := sorry

/-
info: 'e'
-/
-- #guard_msgs in
-- #eval first_non_repeated "test"

/-
info: 'r'
-/
-- #guard_msgs in
-- #eval first_non_repeated "teeter"

/-
info: '5'
-/
-- #guard_msgs in
-- #eval first_non_repeated "1122321235121222"

-- Apps difficulty: introductory
-- Assurance level: unguarded