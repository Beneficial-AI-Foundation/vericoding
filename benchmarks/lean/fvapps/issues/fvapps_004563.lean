-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def wallpaper (l w h : Float) : NumberWord := sorry

/- If either width or length is 0, result is zero -/
-- </vc-definitions>

-- <vc-theorems>
theorem wallpaper_zero {l w h : Float} :
  l * w = 0 → wallpaper l w h = NumberWord.zero := sorry

/- Result is always a valid number word between 0 and 20 -/

theorem wallpaper_valid_output {l w h : Float} :
  ∃ n : NumberWord, wallpaper l w h = n := sorry

/- Non-negative inputs result in non-negative outputs -/

theorem wallpaper_nonneg {l w h : Float} :
  l ≥ 0 → w ≥ 0 → h ≥ 0 → 
  ∃ n : NumberWord, wallpaper l w h = n := sorry

/-
info: 'ten'
-/
-- #guard_msgs in
-- #eval wallpaper 4.0 3.5 3.0

/-
info: 'zero'
-/
-- #guard_msgs in
-- #eval wallpaper 0.0 3.5 3.0

/-
info: 'sixteen'
-/
-- #guard_msgs in
-- #eval wallpaper 6.3 4.5 3.29
-- </vc-theorems>