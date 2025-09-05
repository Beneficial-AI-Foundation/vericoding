Implement a basic calculator to evaluate a simple expression string.

The expression string may contain open ( and closing parentheses ), the plus + or minus sign -, non-negative integers and empty spaces  .

Example 1:

Input: "1 + 1"
Output: 2

Example 2:

Input: " 2-1 + 2 "
Output: 3

Example 3:

Input: "(1+(4+5+2)-3)+(6+8)"
Output: 23
Note:

       You may assume that the given expression is always valid.
       Do not use the eval built-in library function.

def calculate (s : String) : Int := sorry 

theorem single_number {n : Int} (h : -1000 ≤ n ∧ n ≤ 1000) : 
  calculate s!"{n}" = n := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded