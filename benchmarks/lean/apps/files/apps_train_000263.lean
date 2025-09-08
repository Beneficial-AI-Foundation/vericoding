/-
A happy string is a string that:

consists only of letters of the set ['a', 'b', 'c'].
s[i] != s[i + 1] for all values of i from 1 to s.length - 1 (string is 1-indexed).

For example, strings "abc", "ac", "b" and "abcbabcbcb" are all happy strings and strings "aa", "baa" and "ababbc" are not happy strings.
Given two integers n and k, consider a list of all happy strings of length n sorted in lexicographical order.
Return the kth string of this list or return an empty string if there are less than k happy strings of length n.

Example 1:
Input: n = 1, k = 3
Output: "c"
Explanation: The list ["a", "b", "c"] contains all happy strings of length 1. The third string is "c".

Example 2:
Input: n = 1, k = 4
Output: ""
Explanation: There are only 3 happy strings of length 1.

Example 3:
Input: n = 3, k = 9
Output: "cab"
Explanation: There are 12 different happy string of length 3 ["aba", "abc", "aca", "acb", "bab", "bac", "bca", "bcb", "cab", "cac", "cba", "cbc"]. You will find the 9th string = "cab"

Example 4:
Input: n = 2, k = 7
Output: ""

Example 5:
Input: n = 10, k = 100
Output: "abacbabacb"

Constraints:

1 <= n <= 10
1 <= k <= 100
-/

def get_happy_string (n k : Nat) : String :=
  sorry

def all_chars_abc (s : String) : Bool :=
  sorry

def no_adjacent_same (s : String) : Bool := 
  sorry

-- <vc-helpers>
-- </vc-helpers>

def starts_with_a (s : String) : Bool :=
  sorry

theorem happy_string_properties (n k : Nat) 
  (h1 : 0 < n) (h2 : n ≤ 10) (h3 : 0 < k) (h4 : k ≤ 1000) :
  let s := get_happy_string n k
  let max_possible := 3 * 2^(n-1)
  -- Length property
  (s.length = n ∨ s.length = 0) ∧ 
  -- Character set property
  all_chars_abc s ∧
  -- Adjacent character property
  (s.length > 1 → no_adjacent_same s) ∧ 
  -- Empty string property
  ((k > max_possible → s.length = 0) ∧
   (k ≤ max_possible → s.length = n)) :=
  sorry

theorem n1_special_case (k : Nat)
  (h1 : 0 < k) (h2 : k ≤ 10) :
  let s := get_happy_string 1 k
  (k ≤ 3 → (s = "a" ∨ s = "b" ∨ s = "c")) ∧
  (k > 3 → s = "") :=
  sorry

theorem k1_special_case (n : Nat)
  (h1 : 0 < n) (h2 : n ≤ 5) :
  let s := get_happy_string n 1
  s.length = n ∧ 
  starts_with_a s :=
  sorry

/-
info: 'c'
-/
-- #guard_msgs in
-- #eval get_happy_string 1 3

/-
info: 'cab'
-/
-- #guard_msgs in
-- #eval get_happy_string 3 9

/-
info: ''
-/
-- #guard_msgs in
-- #eval get_happy_string 1 4

-- Apps difficulty: interview
-- Assurance level: unguarded