/-
=====Problem Statement=====
The provided code stub reads two integers from STDIN, a and b. Add code to print three lines where:
The first line contains the sum of the two numbers.
The second line contains the difference of the two numbers (first - second).
The third line contains the product of the two numbers.

=====Example=====
a = 3
b = 5

Print the following:
8
-2
15

=====Input Format=====
The first line contains the first integer, a.
The second line contains the second integer, b.

=====Constraints=====
1≤a≤10^10
1≤b≤10^10

=====Output Format=====
Print the three lines as explained above.
-/

-- <vc-helpers>
-- </vc-helpers>

def arithmetic_operations (a b : Int) : String := sorry

theorem arithmetic_operations_format 
  (a b : Int) : 
  let result := arithmetic_operations a b
  let lines := result.splitOn "\n"
  lines.length = 3 ∧ 
  lines.all (fun line => (line.drop (if line.front = '-' then 1 else 0)).all Char.isDigit)
  := sorry

theorem arithmetic_operations_values
  (a b : Int) :
  let result := arithmetic_operations a b
  let lines := result.splitOn "\n"
  let sum_val := lines[0]!.toInt!
  let diff_val := lines[1]!.toInt!
  let prod_val := lines[2]!.toInt!
  sum_val = a + b ∧
  diff_val = a - b ∧ 
  prod_val = a * b
  := sorry

theorem arithmetic_operations_positive
  (a b : Int)
  (ha : 0 ≤ a) (hb : 0 ≤ b)
  (ha_bound : a ≤ 1000) (hb_bound : b ≤ 1000) :
  let result := arithmetic_operations a b
  let lines := result.splitOn "\n"
  let sum_val := lines[0]!.toInt!
  let prod_val := lines[2]!.toInt!
  sum_val ≥ a ∧
  prod_val ≥ min a b
  := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible