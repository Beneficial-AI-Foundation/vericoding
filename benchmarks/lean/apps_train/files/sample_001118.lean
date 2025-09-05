Write a program, which takes an integer N and if the number is less than 10 then display "Thanks for helping Chef!" otherwise print "-1".

-----Input-----

The first line contains an integer T, total number of testcases. Then follow T lines, each line contains an integer N. 

-----Output-----
For each test case, output the given string or -1 depending on conditions, in a new line.

-----Constraints-----
- 1 ≤ T ≤ 1000
- -20 ≤ N ≤ 20

-----Example-----
Input
3 
1
12
-5
Output
Thanks for helping Chef!
-1
Thanks for helping Chef!

def solve_helper_thanks (n : Int) : String := sorry

theorem solve_helper_thanks_result_valid (n : Int) :
  (solve_helper_thanks n = "-1") ∨ 
  (solve_helper_thanks n = "Thanks for helping Chef!") := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded