/-
=====Problem Statement=====
You are given a string S.
Your task is to find out whether is a valid regex or not.

=====Input Format=====
The first line contains integer T, the number of test cases.
The next T lines contains the string S.

=====Constraints=====
0<T<100

=====Output Format=====
Print "True" or "False" for each test case without quotes.
-/

-- <vc-helpers>
-- </vc-helpers>

def is_valid_regex (s : String) : Bool := sorry 

theorem any_string_input_returns_bool (s : String) :
  (is_valid_regex s = true) ∨ (is_valid_regex s = false) :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible