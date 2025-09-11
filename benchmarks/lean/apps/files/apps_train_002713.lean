-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ghostbusters (s : String) : String := sorry

theorem ghostbusters_with_spaces (s : String) (h : String.contains s ' ') :
  ghostbusters s = s.replace " " "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ghostbusters_without_spaces (s : String) (h : ¬String.contains s ' ') :
  ghostbusters s = "You just wanted my autograph didn't you?" := sorry

/-
info: 'Factory'
-/
-- #guard_msgs in
-- #eval ghostbusters "Factor y"

/-
info: 'Office'
-/
-- #guard_msgs in
-- #eval ghostbusters "O  f fi ce"

/-
info: "You just wanted my autograph didn't you?"
-/
-- #guard_msgs in
-- #eval ghostbusters "BusStation"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded