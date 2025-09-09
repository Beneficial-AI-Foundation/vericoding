/-
The chef is trying to solve some pattern problems, Chef wants your help to code it. Chef has one number K to form a new pattern. Help the chef to code this pattern problem.

-----Input:-----
-First-line will contain $T$, the number of test cases. Then the test cases follow.
-Each test case contains a single line of input, one integer $K$.

-----Output:-----
For each test case, output as the pattern.

-----Constraints-----
- $1 \leq T \leq 26$
- $1 \leq K \leq 26$

-----Sample Input:-----
2
2
4

-----Sample Output:-----
A
12
A
12
ABC
1234

-----EXPLANATION:-----
No need, else pattern can be decode easily.
-/

-- <vc-helpers>
-- </vc-helpers>

def generate_pattern (k : Nat) : List String := sorry 

def format_multiple_patterns (cases : List Nat) : List String := sorry

theorem generate_pattern_length (k : Nat) (h : 0 < k ∧ k ≤ 26) :
  (generate_pattern k).length = k := sorry

theorem generate_pattern_alternating (k : Nat) (h : 0 < k ∧ k ≤ 26) (i : Nat) (hi : i < k) :
  let line := (generate_pattern k)[i]'(by 
    rw [generate_pattern_length k h]
    exact hi)
  if i % 2 = 0 
  then ∀ c ∈ line.data, c.isUpper ∧ (c.toNat - 'A'.toNat < i + 1)
  else ∀ c ∈ line.data, c.isDigit := sorry

theorem format_multiple_patterns_length {cases : List Nat} (h : cases ≠ []) 
  (h2 : ∀ k ∈ cases, 0 < k ∧ k ≤ 26) :
  (format_multiple_patterns cases).length = cases.foldl (· + ·) 0 := sorry

theorem format_multiple_patterns_matches {cases : List Nat} (h : cases ≠ [])
  (h2 : ∀ k ∈ cases, 0 < k ∧ k ≤ 26) (pos k : Nat):
  k ∈ cases →
  (format_multiple_patterns cases).take k = generate_pattern k := sorry

-- Apps difficulty: interview
-- Assurance level: guarded