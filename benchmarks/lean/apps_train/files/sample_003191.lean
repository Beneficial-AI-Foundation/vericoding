/-
Write a function 

`titleToNumber(title) or title_to_number(title) or titleToNb title ...`

(depending on the language)

that given a column title as it appears in an Excel sheet, returns its corresponding column number. All column titles will be uppercase.

Examples:
```
titleTonumber('A') === 1
titleTonumber('Z') === 26
titleTonumber('AA') === 27
```
-/

-- <vc-helpers>
-- </vc-helpers>

def titleToNumber (s : String) : Nat := sorry

theorem title_to_number_positive (s : String) (h : s.all (fun c => 'A' ≤ c ∧ c ≤ 'Z')) : 
  titleToNumber s > 0 := sorry

theorem title_to_number_single_char_range (c : Char) (h : 'A' ≤ c ∧ c ≤ 'Z') :
  1 ≤ titleToNumber (String.mk [c]) ∧ titleToNumber (String.mk [c]) ≤ 26 := sorry

theorem title_to_number_recursive (s : String) (c : Char) 
  (h1 : s.all (fun c => 'A' ≤ c ∧ c ≤ 'Z')) 
  (h2 : 'A' ≤ c ∧ c ≤ 'Z') :
  titleToNumber (s.push c) = titleToNumber s * 26 + (c.toNat - 'A'.toNat + 1) := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval title_to_number "A"

/-
info: 26
-/
-- #guard_msgs in
-- #eval title_to_number "Z"

/-
info: 27
-/
-- #guard_msgs in
-- #eval title_to_number "AA"

-- Apps difficulty: introductory
-- Assurance level: guarded