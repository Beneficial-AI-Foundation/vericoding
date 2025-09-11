-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def eval_rpn : List String → Int
  | _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem eval_rpn_empty :
  eval_rpn [] = 0 := by sorry

theorem eval_rpn_single_positive :
  eval_rpn ["5"] = 5 := by sorry

theorem eval_rpn_single_negative : 
  eval_rpn ["-5"] = -5 := by sorry

theorem eval_rpn_addition :
  eval_rpn ["3", "2", "+"] = 5 := by sorry

theorem eval_rpn_subtraction :
  eval_rpn ["3", "2", "-"] = 1 := by sorry

theorem eval_rpn_multiplication :
  eval_rpn ["3", "2", "*"] = 6 := by sorry

theorem eval_rpn_division :
  eval_rpn ["6", "2", "/"] = 3 := by sorry

theorem eval_rpn_negative_division_1 :
  eval_rpn ["6", "-2", "/"] = -3 := by sorry

theorem eval_rpn_negative_division_2 :
  eval_rpn ["-6", "2", "/"] = -3 := by sorry

theorem eval_rpn_negative_multiplication :
  eval_rpn ["-2", "-3", "*"] = 6 := by sorry

theorem eval_rpn_negative_addition :
  eval_rpn ["-1", "1", "+"] = 0 := by sorry

theorem eval_rpn_complex_1 :
  eval_rpn ["2", "1", "+", "3", "*"] = 9 := by sorry

theorem eval_rpn_complex_2 :
  eval_rpn ["4", "13", "5", "/", "+"] = 6 := by sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval eval_rpn ["2", "1", "+", "3", "*"]

/-
info: 6
-/
-- #guard_msgs in
-- #eval eval_rpn ["4", "13", "5", "/", "+"]

/-
info: 22
-/
-- #guard_msgs in
-- #eval eval_rpn ["10", "6", "9", "3", "+", "-11", "*", "/", "*", "17", "+", "5", "+"]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded