-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_rabbits (x y a b : Int) : Int := sorry

theorem solve_rabbits_correct (x y a b jumps : Int) 
  (ha : a > 0) (hb : b > 0) (hjumps : jumps ≥ 0)
  (hy : y = x + (a + b) * jumps) :
  solve_rabbits x y a b = jumps := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_rabbits_impossible (x y a b distance : Int)
  (ha : a > 0) (hb : b > 0) (hdist : distance > 0)
  (hy : y = x + distance)
  (h_not_div : ¬(distance % (a + b) = 0)) : 
  solve_rabbits x y a b = -1 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_rabbits 0 10 2 3

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_rabbits 0 10 3 3

/-
info: 10
-/
-- #guard_msgs in
-- #eval solve_rabbits 900000000 1000000000 1 9999999
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible