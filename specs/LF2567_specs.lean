-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def black_or_white_key (key : Int) : Color :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem returns_valid_color (key : Int) :
  black_or_white_key key = Color.black ∨ black_or_white_key key = Color.white :=
sorry

theorem pattern_repeats_88_keys (key : Int) :
  black_or_white_key key = black_or_white_key (key + 88) :=
sorry

theorem octave_pattern_correct (key : Int) :
  let normalized := ((key - 1) % 88) % 12
  (normalized = 1 ∨ normalized = 4 ∨ normalized = 6 ∨ normalized = 9 ∨ normalized = 11)
    ↔ black_or_white_key key = Color.black :=
sorry

/-
info: 'white'
-/
-- #guard_msgs in
-- #eval black_or_white_key 1

/-
info: 'black'
-/
-- #guard_msgs in
-- #eval black_or_white_key 5

/-
info: 'black'
-/
-- #guard_msgs in
-- #eval black_or_white_key 12

/-
info: 'white'
-/
-- #guard_msgs in
-- #eval black_or_white_key 89

/-
info: 'black'
-/
-- #guard_msgs in
-- #eval black_or_white_key 100

/-
info: 'white'
-/
-- #guard_msgs in
-- #eval black_or_white_key 2017
-- </vc-theorems>