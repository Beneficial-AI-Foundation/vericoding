-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def box_capacity (length width height : Nat) : Nat := sorry

theorem box_capacity_nonneg (l w h : Nat) :
  box_capacity l w h ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem box_capacity_monotonic_length (l w h : Nat) :
  box_capacity (l + 1) w h ≥ box_capacity l w h := sorry

theorem box_capacity_monotonic_width (l w h : Nat) :
  box_capacity l (w + 1) h ≥ box_capacity l w h := sorry

theorem box_capacity_monotonic_height (l w h : Nat) :
  box_capacity l w (h + 1) ≥ box_capacity l w h := sorry

theorem box_capacity_small_dim (w h : Nat) :
  box_capacity 1 w h = 0 := sorry

/-
info: 13824
-/
-- #guard_msgs in
-- #eval box_capacity 32 64 16

/-
info: 3375
-/
-- #guard_msgs in
-- #eval box_capacity 20 20 20

/-
info: 27000
-/
-- #guard_msgs in
-- #eval box_capacity 80 40 20
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible