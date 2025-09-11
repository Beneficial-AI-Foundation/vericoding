-- <vc-preamble>
def watch_pyramid_from_the_side (chars : Option String) : Option String := sorry
def watch_pyramid_from_above (chars : Option String) : Option String := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_visible_characters_of_the_pyramid (chars : Option String) : Int := sorry
def count_all_characters_of_the_pyramid (chars : Option String) : Int := sorry

-- Empty inputs theorem
-- </vc-definitions>

-- <vc-theorems>
theorem empty_inputs {chars : Option String} : 
  chars = none ∨ chars = some "" →
  watch_pyramid_from_the_side chars = chars ∧ 
  watch_pyramid_from_above chars = chars ∧
  count_visible_characters_of_the_pyramid chars = -1 ∧
  count_all_characters_of_the_pyramid chars = -1 := sorry

-- Visible characters theorem 

theorem count_visible_chars {s : String} (h : s.length > 0) :
  count_visible_characters_of_the_pyramid (some s) = 
    (2 * s.length - 1) * (2 * s.length - 1) := sorry

/-
info: None
-/
-- #guard_msgs in
-- #eval watch_pyramid_from_the_side None

/-
info: ''
-/
-- #guard_msgs in
-- #eval watch_pyramid_from_the_side ""

/-
info: -1
-/
-- #guard_msgs in
-- #eval count_visible_characters_of_the_pyramid None

/-
info: expected_side
-/
-- #guard_msgs in
-- #eval watch_pyramid_from_the_side "abc"

/-
info: expected_above
-/
-- #guard_msgs in
-- #eval watch_pyramid_from_above test_str

/-
info: 25
-/
-- #guard_msgs in
-- #eval count_visible_characters_of_the_pyramid test_str

/-
info: 35
-/
-- #guard_msgs in
-- #eval count_all_characters_of_the_pyramid test_str
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded