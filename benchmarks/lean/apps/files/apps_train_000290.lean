/-
You have n  tiles, where each tile has one letter tiles[i] printed on it.
Return the number of possible non-empty sequences of letters you can make using the letters printed on those tiles.

Example 1:
Input: tiles = "AAB"
Output: 8
Explanation: The possible sequences are "A", "B", "AA", "AB", "BA", "AAB", "ABA", "BAA".

Example 2:
Input: tiles = "AAABBC"
Output: 188

Example 3:
Input: tiles = "V"
Output: 1

Constraints:

1 <= tiles.length <= 7
tiles consists of uppercase English letters.
-/

-- <vc-helpers>
-- </vc-helpers>

def numTilePossibilities (s : String) : Nat :=
  sorry

theorem tile_possibilities_bounds {s : String} (h : s.length ≥ 1) (h2 : s.length ≤ 7) :
  let result := numTilePossibilities s
  result ≥ 0 ∧ 
  result ≥ s.data.eraseDups.length - 1 ∧
  result ≤ s.length ^ s.length :=
  sorry

theorem single_tile_case {s : String} (h : s.length = 1) :
  numTilePossibilities s = 1 :=
  sorry

theorem permutations_exceed_unique {s : String} (h : s.length ≥ 2) (h2 : s.length ≤ 7) :
  numTilePossibilities s ≥ s.data.eraseDups.length :=
  sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval numTilePossibilities "AAB"

/-
info: 188
-/
-- #guard_msgs in
-- #eval numTilePossibilities "AAABBC"

/-
info: 1
-/
-- #guard_msgs in
-- #eval numTilePossibilities "V"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible