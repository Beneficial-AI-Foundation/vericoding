/-
Chef has a string of size $N$ which consists only lowercase English alphabet. The chef doesn't like the consonant alphabet at all. So he is thinking of changing every single consonant alphabet to any vowel alphabet. There is some cost for performing this operation.
- Number all alphabet [a,b,c,……,z] as [1,2,3,…..,26]
- So if you want to change c to e then cost will be |e-c| = |5-3| = 2
You need the answer at what minimum cost chef can change every single consonant alphabet to any vowel alphabet. 

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Each test case contains of a single line of input, a string of lowercase alphabet. 

-----Output:-----
For each test case, output in a single line answer.

-----Constraints-----
- $1 \leq T \leq 100$
- $1 \leq |s| \leq 10^2$

-----Sample Input:-----
2
aeiou
dbcc  

-----Sample Output:-----
0
6

-----EXPLANATION:-----
In the first test case, all characters are already vowel so we don't need to change.
In the second tect case
|e-d|=|5-4|=1
|a-b|=|1-2|=1
|a-c|=|1-3|=2
|a-c|=|1-3|=2
1+1+2+2=6
-/

def isVowel (c : Char) : Bool := 
  c = 'a' ∨ c = 'e' ∨ c = 'i' ∨ c = 'o' ∨ c = 'u'

-- <vc-helpers>
-- </vc-helpers>

def minCostVowelTransform (s : String) : Nat :=
sorry

theorem min_cost_non_negative (s : String) :
  minCostVowelTransform s ≥ 0 :=
sorry

theorem vowels_zero_cost (s : String) :
  (∀ c ∈ s.data, isVowel c) → minCostVowelTransform s = 0 :=
sorry

theorem cost_is_sum_of_min_distances (s : String) :
  minCostVowelTransform s = 
    s.data.foldl (fun acc c =>
      if isVowel c then 
        acc
      else
        acc + ['a', 'e', 'i', 'o', 'u'].foldl (fun min_dist v =>
          min min_dist (if c.toNat ≥ v.toNat then c.toNat - v.toNat else v.toNat - c.toNat)
        ) 1000000
    ) 0 :=
sorry

theorem non_vowels_positive_cost (s : String) :
  s ≠ "" →
  (∀ c ∈ s.data, ¬isVowel c) →
  minCostVowelTransform s > 0 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_cost_vowel_transform "aeiou"

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_cost_vowel_transform "dbcc"

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_cost_vowel_transform "bc"

-- Apps difficulty: interview
-- Assurance level: guarded