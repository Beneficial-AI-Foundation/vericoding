/-
The chef is trying to solve some pattern problems, Chef wants your help to code it. Chef has one number K to form a new pattern. Help the chef to code this pattern problem.

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Each test case contains a single line of input, one integer $K$. 

-----Output:-----
For each test case, output as the pattern.

-----Constraints-----
- $1 \leq T \leq 100$
- $1 \leq K \leq 100$

-----Sample Input:-----
5
1
2
3
4
5

-----Sample Output:-----
1
1
32
1
32
654
1
32
654
10987
1
32
654
10987
1514131211

-----EXPLANATION:-----
No need, else pattern can be decode easily.
-/

-- <vc-helpers>
-- </vc-helpers>

def print_pattern (n: Nat) : List String := sorry

theorem print_pattern_basic_2 : 
  print_pattern 2 = ["1", "32"] := sorry

theorem print_pattern_basic_3 :
  print_pattern 3 = ["1", "32", "654"] := sorry

theorem print_pattern_basic_4 :
  print_pattern 4 = ["1", "32", "654", "10987"] := sorry

theorem print_pattern_zero :
  print_pattern 0 = [] := sorry

theorem print_pattern_one :
  print_pattern 1 = ["1"] := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval print_pattern 2

/-
info: expected2
-/
-- #guard_msgs in
-- #eval print_pattern 3

/-
info: expected3
-/
-- #guard_msgs in
-- #eval print_pattern 4

-- Apps difficulty: interview
-- Assurance level: unguarded