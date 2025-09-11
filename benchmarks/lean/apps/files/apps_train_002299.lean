-- <vc-preamble>
def third_max (nums : List Int) : Int := sorry

def max (nums : List Int) : Int := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def uniqueSorted (nums : List Int) : List Int := sorry

theorem third_max_is_in_list {nums : List Int} (h : nums ≠ []) :
  third_max nums ∈ nums := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 1
-/
-- #guard_msgs in
-- #eval third_max [3, 2, 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval third_max [1, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval third_max [2, 2, 3, 1]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible