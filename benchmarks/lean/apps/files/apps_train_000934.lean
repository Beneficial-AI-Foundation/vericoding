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
21
1
123
21
1
4321
123
21
1

-----EXPLANATION:-----
No need, else pattern can be decode easily.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_pattern (k: Nat) : Array String := sorry

theorem solve_pattern_length (k: Nat) (h: k > 0) (h2: k ≤ 100) :
  (solve_pattern k).size = k := sorry

theorem solve_pattern_all_digits (k: Nat) (h: k > 0) (h2: k ≤ 100) (i: Nat) (h3: i < k) :
  let result := solve_pattern k
  result[i]!.all Char.isDigit = true := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible