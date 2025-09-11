-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mod256_without_mod (x : Int) : Int := sorry

theorem mod256_matches_regular_mod (x : Int) :
  mod256_without_mod x = x % 256 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_range (x : Int) :
  0 ≤ mod256_without_mod x ∧ mod256_without_mod x ≤ 255 := sorry

theorem periodic_property (x n : Int) : 
  mod256_without_mod x = mod256_without_mod (x + n * 256) := sorry

/-
info: 254
-/
-- #guard_msgs in
-- #eval mod256_without_mod 254

/-
info: 0
-/
-- #guard_msgs in
-- #eval mod256_without_mod 256

/-
info: 254
-/
-- #guard_msgs in
-- #eval mod256_without_mod -258
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded