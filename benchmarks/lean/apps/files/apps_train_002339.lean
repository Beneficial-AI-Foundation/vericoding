/-
Given a positive integer, return its corresponding column title as appear in an Excel sheet.

For example:

    1 -> A
    2 -> B
    3 -> C
    ...
    26 -> Z
    27 -> AA
    28 -> AB 
    ...

Example 1:

Input: 1
Output: "A"

Example 2:

Input: 28
Output: "AB"

Example 3:

Input: 701
Output: "ZY"
-/

-- <vc-helpers>
-- </vc-helpers>

def convertToExcelTitle (n : Nat) : String := sorry

def colNumFromStr (s : String) : Nat := sorry

theorem convert_to_excel_title_properties (n : Nat) 
  (h1 : n > 0) (h2 : n ≤ 1000000) :
  let result := convertToExcelTitle n
  -- Result is nonempty
  String.length result > 0 ∧ 
  -- Result converts back to original number
  colNumFromStr result = n :=
sorry

theorem single_letter_cases (n : Nat)
  (h1 : n > 0) (h2 : n ≤ 26) :
  let result := convertToExcelTitle n
  String.length result = 1 :=
sorry

theorem edge_cases :
  convertToExcelTitle 1 = "A" ∧
  convertToExcelTitle 26 = "Z" ∧ 
  convertToExcelTitle 27 = "AA" :=
sorry

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval convert_to_excel_title 1

/-
info: 'AB'
-/
-- #guard_msgs in
-- #eval convert_to_excel_title 28

/-
info: 'ZY'
-/
-- #guard_msgs in
-- #eval convert_to_excel_title 701

-- Apps difficulty: introductory
-- Assurance level: unguarded