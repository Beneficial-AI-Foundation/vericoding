/-
You are given a string S of length n with each character being one of the first m lowercase English letters. 

Calculate how many different strings T of length n composed from the first m lowercase English letters exist such that the length of LCS (longest common subsequence) between S and T is n - 1.

Recall that LCS of two strings S and T is the longest string C such that C both in S and T as a subsequence.

-----Input-----

The first line contains two numbers n and m denoting the length of string S and number of first English lowercase characters forming the character set for strings (1 ≤ n ≤ 100 000, 2 ≤ m ≤ 26).

The second line contains string S.

-----Output-----

Print the only line containing the answer.

-----Examples-----
Input
3 3
aaa

Output
6

Input
3 3
aab

Output
11

Input
1 2
a

Output
1

Input
10 9
abacadefgh

Output
789

-----Note-----

For the first sample, the 6 possible strings T are: aab, aac, aba, aca, baa, caa. 

For the second sample, the 11 possible strings T are: aaa, aac, aba, abb, abc, aca, acb, baa, bab, caa, cab.

For the third sample, the only possible string T is b.
-/

-- <vc-helpers>
-- </vc-helpers>

def calculate_lcs_strings (n m : Nat) (s : String) : Nat :=
  sorry

theorem result_bounds 
  (n m : Nat) (s : String)
  (hn : n > 0) (hm : m ≥ 2)
  (hs : String.length s = n) :
  let result := calculate_lcs_strings n m s
  0 ≤ result ∧ result ≤ n * n * (m-1) :=
sorry

theorem decreasing_m_property
  (n m : Nat) (s : String)
  (hn : n > 0) (hm : m > 2)
  (hs : String.length s = n) :
  let result1 := calculate_lcs_strings n m s
  let result2 := calculate_lcs_strings n (m-1) s
  result1 ≥ result2 :=
sorry

theorem alternating_strings_property
  (n m : Nat) (s : String)
  (hn : n > 1) (hm : m ≥ 2)
  (hs : s = String.mk (List.map (fun i => if i % 2 = 0 then 'a' else 'b') (List.range n))) :
  calculate_lcs_strings n m s > 0 :=
sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval calculate_lcs_strings 3 3 "aaa"

/-
info: 11
-/
-- #guard_msgs in
-- #eval calculate_lcs_strings 3 3 "aab"

/-
info: 789
-/
-- #guard_msgs in
-- #eval calculate_lcs_strings 10 9 "abacadefgh"

-- Apps difficulty: competition
-- Assurance level: unguarded