-- <vc-helpers>
-- </vc-helpers>

def min_start_value (nums : List Int) : Int := sorry

def running_sums (start : Int) (nums : List Int) : List Int :=
  match nums with
  | [] => [start]
  | x::xs => let rest := running_sums (start + x) xs
             start :: rest

theorem min_start_single_element (x : Int) :
  let start := min_start_value [x]
  start ≥ 1 ∧ start + x ≥ 1 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval min_start_value [-3, 2, -3, 4, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_start_value [1, 2]

/-
info: 5
-/
-- #guard_msgs in
-- #eval min_start_value [1, -2, -3]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible