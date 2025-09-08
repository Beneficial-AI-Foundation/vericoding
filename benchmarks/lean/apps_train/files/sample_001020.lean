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
0
*1
**2
0
*1
**2
***3
0
*1
**2
***3
****4

-----EXPLANATION:-----
No need, else pattern can be decode easily.
-/

-- <vc-helpers>
-- </vc-helpers>

def generatePattern (k : Nat) : List String := sorry

theorem generate_pattern_length {k : Nat} :
  List.length (generatePattern k) = k + 1 := sorry

theorem generate_pattern_first_element {k : Nat} :
  List.head! (generatePattern k) = "0" := sorry

theorem generate_pattern_stars_count {k : Nat} {i : Nat} (h : i > 0) (h2 : i ≤ k) :
  let row := (generatePattern k).get! i
  let count := row.foldl (fun acc c => if c = '*' then acc + 1 else acc) 0
  count = i := sorry

theorem generate_pattern_row_format {k : Nat} {i : Nat} (h : i > 0) (h2 : i ≤ k) :
  let row := (generatePattern k).get! i
  row = String.mk (List.replicate i '*') ++ toString i := sorry

theorem generate_pattern_empty :
  generatePattern 0 = ["0"] := sorry

/-
info: ['0', '*1', '**2']
-/
-- #guard_msgs in
-- #eval generate_pattern 2

/-
info: ['0', '*1', '**2', '***3']
-/
-- #guard_msgs in
-- #eval generate_pattern 3

/-
info: ['0', '*1', '**2', '***3', '****4']
-/
-- #guard_msgs in
-- #eval generate_pattern 4

-- Apps difficulty: interview
-- Assurance level: unguarded