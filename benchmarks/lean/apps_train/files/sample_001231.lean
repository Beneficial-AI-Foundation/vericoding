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
3
2
3
4

-----Sample Output:-----
1121
1222
112131
122232
132333
11213141
12223242
13233343
14243444

-----EXPLANATION:-----
No need, else pattern can be decode easily.
-/

-- <vc-helpers>
-- </vc-helpers>

def generate_pattern (k : Nat) : Array String := sorry

theorem generate_pattern_length (k : Nat) (h : k > 0) : 
  (generate_pattern k).size = k := sorry

theorem generate_pattern_numeric (k : Nat) (h : k > 0) :
  ∀ s ∈ (generate_pattern k).data, ∀ c ∈ s.data, c.isDigit := sorry

/-
info: ['1121', '1222']
-/
-- #guard_msgs in
-- #eval generate_pattern 2

/-
info: ['112131', '122232', '132333']
-/
-- #guard_msgs in
-- #eval generate_pattern 3

/-
info: ['11213141', '12223242', '13233343', '14243444']
-/
-- #guard_msgs in
-- #eval generate_pattern 4

-- Apps difficulty: interview
-- Assurance level: unguarded