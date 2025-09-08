/-
You are given a string s, and an array of pairs of indices in the string pairs where pairs[i] = [a, b] indicates 2 indices(0-indexed) of the string.
You can swap the characters at any pair of indices in the given pairs any number of times.
Return the lexicographically smallest string that s can be changed to after using the swaps.

Example 1:
Input: s = "dcab", pairs = [[0,3],[1,2]]
Output: "bacd"
Explaination: 
Swap s[0] and s[3], s = "bcad"
Swap s[1] and s[2], s = "bacd"

Example 2:
Input: s = "dcab", pairs = [[0,3],[1,2],[0,2]]
Output: "abcd"
Explaination: 
Swap s[0] and s[3], s = "bcad"
Swap s[0] and s[2], s = "acbd"
Swap s[1] and s[2], s = "abcd"
Example 3:
Input: s = "cba", pairs = [[0,1],[1,2]]
Output: "abc"
Explaination: 
Swap s[0] and s[1], s = "bca"
Swap s[1] and s[2], s = "bac"
Swap s[0] and s[1], s = "abc"

Constraints:

1 <= s.length <= 10^5
0 <= pairs.length <= 10^5
0 <= pairs[i][0], pairs[i][1] < s.length
s only contains lower case English letters.
-/

-- <vc-helpers>
-- </vc-helpers>

def smallest_string_with_swaps (s : String) (pairs : List (List Nat)) : String :=
  sorry

theorem result_length_matches_input (s : String) (pairs : List (List Nat)) :
  pairs.all (fun p => p.length = 2 ∧ p[0]! < s.length ∧ p[1]! < s.length) →
  (smallest_string_with_swaps s pairs).length = s.length :=
  sorry

theorem empty_pairs_returns_same_string (s : String) :
  smallest_string_with_swaps s [] = s :=
  sorry

theorem result_is_permutation (s : String) (pairs : List (List Nat)) :
  pairs.all (fun p => p.length = 2 ∧ p[0]! < s.length ∧ p[1]! < s.length) →
  ∃ perm : List Char → List Char, 
    perm (smallest_string_with_swaps s pairs).toList = s.toList ∧
    ∀ x y, perm x = perm y → x = y :=
  sorry

theorem result_is_lex_minimal (s : String) (pairs : List (List Nat)) :
  pairs.all (fun p => p.length = 2 ∧ p[0]! < s.length ∧ p[1]! < s.length) →
  ∀ i j, i < s.length → j < s.length →
  pairs.any (fun p => p[0]! = i ∧ p[1]! = j) →
  let result := smallest_string_with_swaps s pairs
  result.data[i]! ≤ result.data[j]! :=
  sorry

/-
info: 'bacd'
-/
-- #guard_msgs in
-- #eval smallest_string_with_swaps "dcab" [[0, 3], [1, 2]]

/-
info: 'abcd'
-/
-- #guard_msgs in
-- #eval smallest_string_with_swaps "dcab" [[0, 3], [1, 2], [0, 2]]

/-
info: 'abc'
-/
-- #guard_msgs in
-- #eval smallest_string_with_swaps "cba" [[0, 1], [1, 2]]

-- Apps difficulty: interview
-- Assurance level: unguarded