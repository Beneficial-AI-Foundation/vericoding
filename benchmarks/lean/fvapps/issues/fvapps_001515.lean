-- <vc-preamble>
def Int.abs (n : Int) : Int := 
  if n ≥ 0 then n else -n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_kth_angle (N : Nat) (A : Int) (K : Nat) : Int × Nat := sorry

theorem first_angle_matches {N : Nat} {A : Int} 
  (hN : N ≥ 3) (hN2 : N ≤ 100) (hA : 0 ≤ A) (hA2 : A ≤ 360) :
  let (num, den) := find_kth_angle N A 1
  Int.div num den = A := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: (60, 1)
-/
-- #guard_msgs in
-- #eval find_kth_angle 3 30 2

/-
info: (90, 1)
-/
-- #guard_msgs in
-- #eval find_kth_angle 4 90 2

/-
info: (108, 1)
-/
-- #guard_msgs in
-- #eval find_kth_angle 5 72 3
-- </vc-theorems>