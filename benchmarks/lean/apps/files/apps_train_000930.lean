/-
The chef is trying to solve some pattern problems, Chef wants your help to code it. Chef has one number K to form a new pattern. Help the chef to code this pattern problem.

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Each test case contains a single line of input, one integer $K$. 

-----Output:-----
For each test case, output as the pattern.

-----Constraints-----
- $1 \leq T \leq 50$
- $1 \leq K \leq 50$

-----Sample Input:-----
5
1
2
3
4
5

-----Sample Output:-----
*
*
***
*
* *
*****
*
* *
*   *
*******
*
* *
*   *
*     *
*********   

-----EXPLANATION:-----
No need, else pattern can be decode easily.
-/

-- <vc-helpers>
-- </vc-helpers>

def generate_pattern (k : Nat) : List String := sorry

theorem minimal_cases:
  generate_pattern 1 = ["*"] ∧
  generate_pattern 2 = ["*", "***"] ∧
  generate_pattern 3 = ["  *  ", " * * ", "*****"] :=
sorry

theorem pattern_length (k : Nat) (h : k > 0):
  (generate_pattern k).length = k :=
sorry

theorem pattern_valid_chars (k : Nat) (h : k > 0):
  ∀ line ∈ generate_pattern k,
  ∀ c ∈ line.data, c = ' ' ∨ c = '*' :=
sorry

theorem last_line_asterisks (k : Nat) (h : k > 1):
  (generate_pattern k).getLast (by sorry) =
  String.mk (List.replicate (2*k - 1) '*') :=
sorry

theorem first_line_centered (k : Nat) (h : k > 2):
  (generate_pattern k).head! =
  String.mk (List.replicate (k-1) ' ' ++ '*' :: List.replicate (k-1) ' ') :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded