/-
=====Function Descriptions=====
input()
In Python 2, the expression input() is equivalent to eval(raw _input(prompt)).

Code
>>> input()  
1+2
3
>>> company = 'HackerRank'
>>> website = 'www.hackerrank.com'
>>> input()
'The company name: '+company+' and website: '+website
'The company name: HackerRank and website: www.hackerrank.com'

=====Problem Statement=====
You are given a polynomial P of a single indeterminate (or variable), x. You are also given the values of x and k. Your task is to verify if P(x) = k.

=====Output Format=====
Print True if P(x) = k. Otherwise, print False.
-/

-- <vc-helpers>
-- </vc-helpers>

def is_polynomial_equal (x : Int) (expected : Int) (poly_str : String) : Bool := sorry

theorem constant_polynomial_true (x : Int) : 
  is_polynomial_equal x 5 "5" = true := sorry

theorem constant_polynomial_false (x : Int) :
  is_polynomial_equal x 6 "5" = false := sorry

theorem zero_polynomial :
  is_polynomial_equal 0 0 "0" = true := sorry

theorem linear_polynomial :
  is_polynomial_equal 1 1 "x" = true := sorry

theorem quadratic_polynomial :
  is_polynomial_equal 2 4 "x**2" = true := sorry

theorem negative_quadratic :
  is_polynomial_equal (-1) 1 "x**2" = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_polynomial_equal 1 4 "x**3 + x**2 + x + 1"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_polynomial_equal 2 20 "x**3 + x**2 + x + 1"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_polynomial_equal 0 1 "x**3 + x**2 + x + 1"

-- Apps difficulty: introductory
-- Assurance level: unguarded