-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numTilePossibilities (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible