-- <vc-preamble>
def expression_out (expr : String) : String := sorry

def VALID_OPERATORS : List String := ["+", "-", "*", "/", "**", "=", "!="]
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def VALID_NUMBERS : List String := ["1", "2", "3", "4", "5", "6", "7", "8", "9", "10"]

theorem valid_expressions_return_valid_string {expr : String} 
  (h1 : expr.splitOn " " = [num1, op, num2])
  (h2 : num1 ∈ VALID_NUMBERS)
  (h3 : op ∈ VALID_OPERATORS) 
  (h4 : num2 ∈ VALID_NUMBERS) :
  ∃ result : String, 
    expression_out expr = result ∧ 
    result ≠ "That's not an operator!" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_expressions_return_error_message {expr : String}
  (h : ¬(∃ num1 op num2, expr.splitOn " " = [num1, op, num2] ∧ 
                         num1 ∈ VALID_NUMBERS ∧
                         op ∈ VALID_OPERATORS ∧
                         num2 ∈ VALID_NUMBERS)) :
  expression_out expr = "That's not an operator!" := sorry

theorem output_format {expr : String} 
  (h : expr = "1 + 2") :
  let result := expression_out expr
  ∀ word ∈ result.splitOn " ",
    word.front.isUpper = true ∧
    ¬result.back = ' ' := sorry

/-
info: 'One Plus Three'
-/
-- #guard_msgs in
-- #eval expression_out "1 + 3"

/-
info: 'Six To The Power Of Nine'
-/
-- #guard_msgs in
-- #eval expression_out "6 ** 9"

/-
info: 'Eight Does Not Equal Five'
-/
-- #guard_msgs in
-- #eval expression_out "8 != 5"
-- </vc-theorems>