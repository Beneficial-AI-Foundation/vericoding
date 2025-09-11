-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def beeramid (bonus: Int) (price: Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem beeramid_non_negative (bonus price: Int) (h: price > 0) : 
  beeramid bonus price ≥ 0 := 
  sorry

theorem negative_bonus_gives_zero (bonus price: Int) (h1: bonus < 0) (h2: price > 0) :
  beeramid bonus price = 0 :=
  sorry

theorem monotonic_bonus (bonus price: Int) (h1: bonus ≥ 0) (h2: price > 0) :
  beeramid (bonus + price) price ≥ beeramid bonus price :=
  sorry

theorem monotonic_price (bonus price: Int) (h1: bonus ≥ 0) (h2: price > 0) :
  beeramid bonus (2 * price) ≤ beeramid bonus price :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval beeramid 9 2

/-
info: 3
-/
-- #guard_msgs in
-- #eval beeramid 21 1.5

/-
info: 0
-/
-- #guard_msgs in
-- #eval beeramid -1 4
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded