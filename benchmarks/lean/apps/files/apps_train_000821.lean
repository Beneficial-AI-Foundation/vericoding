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
5
3
4

-----Sample Output:-----
1   1
2 2
3
4 4
5   5
1 1
2
3 3
1  1
22
33
4  4

-----EXPLANATION:-----
No need, else pattern can be decode easily.
-/

-- <vc-helpers>
-- </vc-helpers>

def solvePattern (k: Nat) : List String := sorry

theorem pattern_length_matches_input {k: Nat} (h: k ≥ 2) (h2: k ≤ 100) : 
  (solvePattern k).length = k := sorry

theorem each_line_has_correct_number {k: Nat} (h: k ≥ 2) (h2: k ≤ 100) :
  ∀ i: Nat, i < k → 
    let line := (solvePattern k).get ⟨i, by sorry⟩
    line.contains '1' ∧ line.length > 0 := sorry

theorem whitespace_structure {k: Nat} (h: k ≥ 2) (h2: k ≤ 100) :
  let pattern := solvePattern k
  if k % 2 = 0 then
    ∀ i: Nat, i < k → 
      let line := pattern.get ⟨i, by sorry⟩
      let spaces := line.data.filter (fun x => x = ' ')
      spaces.length = 0 ∨ spaces.length = 2
  else
    let middle_idx := k / 2
    let middle_line := pattern.get ⟨middle_idx, by sorry⟩
    (middle_line.data.filter (fun x => x = ' ')).length = 0 ∧
    ∀ i: Nat, i < k → i ≠ middle_idx → 
      let line := pattern.get ⟨i, by sorry⟩
      (line.data.filter (fun x => x = ' ')).length > 0 := sorry

theorem line_endpoints {k: Nat} (h: k ≥ 2) (h2: k ≤ 100) :
  let pattern := solvePattern k
  let first := pattern.get ⟨0, by sorry⟩
  let last := pattern.get ⟨k-1, by sorry⟩
  first.startsWith "1" ∧ 
  first.endsWith "1" ∧
  last.startsWith (toString k) ∧
  last.endsWith (toString k) := sorry

-- Apps difficulty: interview
-- Assurance level: guarded