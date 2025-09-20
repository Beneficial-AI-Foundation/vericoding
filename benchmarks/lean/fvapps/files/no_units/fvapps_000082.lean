-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>