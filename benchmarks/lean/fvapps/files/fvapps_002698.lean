-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_screen_height (width : Nat) (ratio : String) : String := sorry

theorem find_screen_height_format (width : Nat) (ratio : String)
  (h : width > 0)
  (h2 : ∃ a b, ratio = s!"{a}:{b}" ∧ a > 0 ∧ b > 0) :
  ∃ w h : Nat, find_screen_height width ratio = s!"{w}x{h}" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_screen_height_width_matches (width : Nat) (ratio : String)
  (h : width > 0)
  (h2 : ∃ a b, ratio = s!"{a}:{b}" ∧ a > 0 ∧ b > 0) :
  let result := find_screen_height width ratio
  let w := result.splitOn "x" |>.head!
  w.toNat? = some width := sorry

theorem find_screen_height_positive (width : Nat) (ratio : String)
  (h : width > 0) 
  (h2 : ∃ a b, ratio = s!"{a}:{b}" ∧ a > 0 ∧ b > 0) :
  let result := find_screen_height width ratio
  let h := result.splitOn "x" |>.getLast!
  (h.toNat?).isSome ∧ (h.toNat?).get! > 0 := sorry

theorem find_screen_height_ratio_valid (width : Nat) (ratio : String)
  (h : width > 0)
  (h2 : ∃ a b, ratio = s!"{a}:{b}" ∧ a > 0 ∧ b > 0) :
  let result := find_screen_height width ratio
  let h := (result.splitOn "x" |>.getLast!).toNat?.get!
  let a := (ratio.splitOn ":" |>.head!).toNat?.get!
  let b := (ratio.splitOn ":" |>.getLast!).toNat?.get!
  h = width / a * b := sorry
-- </vc-theorems>