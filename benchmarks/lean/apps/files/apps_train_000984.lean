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
4
1
2
3
4

-----Sample Output:-----
2
24
68
246
81012
141618
2468
10121416
18202224
26283032

-----EXPLANATION:-----
No need, else pattern can be decode easily.
-/

-- <vc-helpers>
-- </vc-helpers>

def generate_pattern (k : Nat) : List String := sorry

theorem pattern_only_digits (k : Nat) (h : 0 < k ∧ k ≤ 10) :
  let pattern := generate_pattern k
  ∀ row ∈ pattern, ∀ c ∈ row.data, '0' ≤ c ∧ c ≤ '9' := sorry

theorem pattern_first_row_starts_with_two (k : Nat) (h : 0 < k ∧ k ≤ 10) :
  let pattern := generate_pattern k
  pattern.head!.data.head! = '2' := sorry

theorem pattern_rows_nonempty (k : Nat) (h : 0 < k ∧ k ≤ 10) :
  let pattern := generate_pattern k
  ∀ row ∈ pattern, row.length > 0 := sorry

theorem pattern_base_cases :
  generate_pattern 1 = ["2"] ∧
  generate_pattern 2 = ["24", "68"] := sorry

/-
info: ['2']
-/
-- #guard_msgs in
-- #eval generate_pattern 1

/-
info: ['24', '68']
-/
-- #guard_msgs in
-- #eval generate_pattern 2

/-
info: ['246', '81012', '141618']
-/
-- #guard_msgs in
-- #eval generate_pattern 3

-- Apps difficulty: interview
-- Assurance level: unguarded