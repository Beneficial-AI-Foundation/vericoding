/-
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
-/

def calculate (s : String) : Int := sorry 

theorem single_number {n : Int} (h : -1000 ≤ n ∧ n ≤ 1000) : 
  calculate s!"{n}" = n := sorry

-- <vc-helpers>
-- </vc-helpers>

def makeParens (n : Nat) : String := 
  match n with
  | 0 => ""
  | n+1 => "(" ++ makeParens n

theorem addition {a b : Int} (h : -100 ≤ a ∧ a ≤ 100 ∧ -100 ≤ b ∧ b ≤ 100) :
  calculate s!"{a}+{b}" = a + b := sorry

theorem nested_parentheses {n : Int} (h : -50 ≤ n ∧ n ≤ 50) :
  calculate s!"{makeParens n.toNat}1{makeParens n.toNat}" = 1 := sorry

theorem parentheses_operations {a b : Int} (h : -50 ≤ a ∧ a ≤ 50 ∧ -50 ≤ b ∧ b ≤ 50) :
  calculate s!"({a})+({b})" = a + b ∧ 
  calculate s!"({a})-({b})" = a - b := sorry

theorem whitespace_invariance (spaces : String) (h : ∀ c ∈ spaces.data, c = ' ') :
  calculate "1+2" = calculate s!"{spaces}1{spaces}+{spaces}2{spaces}" := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval calculate ""1 + 1""

/-
info: 3
-/
-- #guard_msgs in
-- #eval calculate "" 2-1 + 2 ""

/-
info: 23
-/
-- #guard_msgs in
-- #eval calculate ""(1+(4+5+2)-3)+(6+8)""

-- Apps difficulty: interview
-- Assurance level: unguarded