/-
You are given a string $s$. And you have a function $f(x)$ defined as:
f(x) = 1, if $x$ is a vowel
f(x) = 0, if $x$ is a constant

Your task is to apply the above function on all the characters in the string s and convert 
the obtained binary string in decimal number $M$.
Since the number $M$ can be very large, compute it modulo $10^9+7$. 

-----Input:-----
- The first line of the input contains a single integer $T$ i.e the no. of test cases. 
- Each test line contains one String $s$ composed of lowercase English alphabet letters. 

-----Output:-----
For each case, print a single line containing one integer $M$ modulo $10^9 + 7$.

-----Constraints-----
- $1 ≤ T ≤ 50$
- $|s|≤10^5$

-----Subtasks-----
- 20 points : $|s|≤30$
- 80 points : $ \text{original constraints}$

-----Sample Input:-----
1
hello

-----Sample Output:-----
9
-/

def binaryStringToDecimal (s : String) : Nat := sorry

theorem result_in_valid_range (s : String) (h : s.length > 0) : 
  binaryStringToDecimal s < 10^9 + 7 ∧ binaryStringToDecimal s ≥ 0 := sorry

-- <vc-helpers>
-- </vc-helpers>

def isVowel (c : Char) : Bool := sorry

theorem all_vowels_max_value (s : String) (h : s.length > 0) 
  (h2 : ∀ c ∈ s.data, isVowel c) :
  binaryStringToDecimal s = (2^s.length - 1) % (10^9 + 7) := sorry

theorem all_consonants_zero (s : String) (h : s.length > 0)
  (h2 : ∀ c ∈ s.data, ¬isVowel c) :
  binaryStringToDecimal s = 0 := sorry

theorem same_vowel_positions_equal (s1 s2 : String) 
  (h1 : s1.length > 0)
  (h2 : s1.length = s2.length)
  (h3 : ∀ (i : String.Pos), isVowel (s1.get i) = isVowel (s2.get i)) :
  binaryStringToDecimal s1 = binaryStringToDecimal s2 := sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval binary_string_to_decimal "hello"

/-
info: 31
-/
-- #guard_msgs in
-- #eval binary_string_to_decimal "aeiou"

/-
info: 0
-/
-- #guard_msgs in
-- #eval binary_string_to_decimal "xyz"

-- Apps difficulty: interview
-- Assurance level: guarded