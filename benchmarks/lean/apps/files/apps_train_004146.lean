-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validSmiley (s : String) : Bool := sorry
def countSmileys (arr : List String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_matches_valid_check {arr : List String} :
  countSmileys arr = (arr.filter validSmiley).length := sorry

theorem count_is_nonnegative {arr : List String} :
  countSmileys arr ≥ 0 := sorry

theorem count_bounded_by_length {arr : List String} :
  countSmileys arr ≤ arr.length := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_smileys []

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_smileys [":D", ":~)", ";~D", ":)"]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_smileys [";]", ":[", ";*", ":$", ";-D"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded