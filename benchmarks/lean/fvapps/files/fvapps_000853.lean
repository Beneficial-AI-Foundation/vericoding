-- <vc-preamble>
def abs (n : Nat) : Nat := 
  if n ≥ 0 then n else 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_catch_thief (x y k n : Nat) : String := sorry

theorem catch_thief_output_validity (x y k n : Nat) (h : k > 0) (h' : n > 0) :
  can_catch_thief x y k n = "Yes" ∨ can_catch_thief x y k n = "No" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem catch_thief_distance_divisible (x y k n : Nat) (h : k > 0) (h' : n > 0) :
  let distance := if x ≥ y then x - y else y - x
  can_catch_thief x y k n = "Yes" ↔ distance % (2 * k) = 0 := sorry

theorem catch_thief_symmetric (x y k n : Nat) (h : k > 0) (h' : n > 0) :
  can_catch_thief x y k n = can_catch_thief y x k n := sorry

theorem catch_thief_translation_invariant (x y k n offset : Nat) (h : k > 0) (h' : n > 0) :
  can_catch_thief (x + offset) (y + offset) k n = can_catch_thief x y k n := sorry

theorem catch_thief_same_position (x k n : Nat) (h : k > 0) (h' : n > 0) :
  can_catch_thief x x k n = "Yes" := sorry
-- </vc-theorems>