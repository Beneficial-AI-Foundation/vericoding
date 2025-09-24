-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rad_ladies (s : String) : String := sorry

theorem rad_ladies_name_preserved {s : String} (h : s ≠ "") :
  let result := rad_ladies (s ++ "!")
  (result.startsWith s) ∧ (result.endsWith "!") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rad_ladies_idempotent (s : String) :
  rad_ladies (rad_ladies s) = rad_ladies s := sorry
-- </vc-theorems>