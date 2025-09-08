/-
Chef Al Gorithm was reading a book about climate and oceans when he encountered the word “glaciological”. He thought it was quite curious, because it has the following interesting property: For every two letters in the word, if the first appears x times and the second appears y times, then |x - y| ≤ 1.
Chef Al was happy about this and called such words 1-good words. He also generalized the concept: He said a word was K-good if for every two letters in the word, if the first appears x times and the second appears y times, then |x - y| ≤ K.
Now, the Chef likes K-good words a lot and so was wondering: Given some word w, how many letters does he have to remove to make it K-good?

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.
Each test case consists of a single line containing two things: a word w and an integer K, separated by a space.

-----Output-----
For each test case, output a single line containing a single integer: the minimum number of letters he has to remove to make the word K-good.

-----Constraints-----
- 1 ≤ T ≤ 30
- 1 ≤ |w| ≤ 105
- 0 ≤ K ≤ 105
- w contains only lowercase English letters.

-----Example-----
Input:
4
glaciological 1
teammate 0
possessions 3
defenselessness 3

Output:
0
0
1
2

-----Explanation-----
Example case 1. The word “glaciological” is already 1-good, so the Chef doesn't have to remove any letter.
Example case 2. Similarly, “teammate” is already 0-good.
Example case 3. The word “possessions” is 4-good. To make it 3-good, the Chef can remove the last s to make “possession”.
Example case 4. The word “defenselessness” is 4-good. To make it 3-good, Chef Al can remove an s and an e to make, for example, “defenslesness”. Note that the word doesn't have to be a valid English word.
-/

-- <vc-helpers>
-- </vc-helpers>

def min_remove_for_kgood (s : String) (k : Nat) : Nat :=
  sorry

theorem min_remove_nonnegative (s : String) (k : Nat) :
  min_remove_for_kgood s k ≥ 0 :=
sorry

theorem min_remove_bounded (s : String) (k : Nat) :
  min_remove_for_kgood s k ≤ s.length :=
sorry

theorem min_remove_large_k (s : String) (k : Nat) :
  s.length > 0 →
  k ≥ s.length →
  min_remove_for_kgood s k = 0 :=
sorry

theorem min_remove_single_char (s : String) :
  s.length = 1 →
  min_remove_for_kgood s 0 = 0 :=
sorry

theorem min_remove_empty_string :
  ∀ k, min_remove_for_kgood "" k = 0 :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible