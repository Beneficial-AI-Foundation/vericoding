-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minimumSwap (s1 s2 : List XY) : Int := sorry

theorem string_length_equal (s1 s2 : List XY) :
  minimumSwap s1 s2 ≠ -1 → s1.length = s2.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_bounds (s1 s2 : List XY) : 
  let result := minimumSwap s1 s2
  result ≠ -1 → 0 ≤ result ∧ result ≤ s1.length := sorry

theorem invalid_case_parity (s1 s2 : List XY) :
  let xy := (List.zip s1 s2).filter (fun p => decide (p.1 = XY.x) && decide (p.2 = XY.y)) |>.length
  let yx := (List.zip s1 s2).filter (fun p => decide (p.1 = XY.y) && decide (p.2 = XY.x)) |>.length
  (xy + yx) % 2 = 1 → minimumSwap s1 s2 = -1 := sorry

theorem identical_strings_no_swaps (s : List XY) :
  minimumSwap s s = 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval minimumSwap "xx" "yy"

/-
info: 2
-/
-- #guard_msgs in
-- #eval minimumSwap "xy" "yx"

/-
info: -1
-/
-- #guard_msgs in
-- #eval minimumSwap "xx" "xy"
-- </vc-theorems>