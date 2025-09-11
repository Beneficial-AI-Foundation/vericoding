-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 1000000007

def calculate_arrangements (k : Nat) (colors : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_color_returns_one (n : Nat) :
  calculate_arrangements 1 [n] = 1 :=
  sorry

theorem unit_colors (k : Nat) :
  let colors := List.replicate k 1
  calculate_arrangements k colors = 1 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval calculate_arrangements 3 [2, 2, 1]

/-
info: 1680
-/
-- #guard_msgs in
-- #eval calculate_arrangements 4 [1, 2, 3, 4]

/-
info: 1
-/
-- #guard_msgs in
-- #eval calculate_arrangements 1 [5]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible