-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def half_life (n0 : Float) (n : Float) (t : Int) : Float := sorry

theorem half_life_positive (n0 : Float) (n : Float) (t : Int)
  (h1 : n0 > 0)
  (h2 : n > 0)
  (h3 : n < n0)
  (h4 : t > 0) :
  half_life n0 n t > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem half_life_inverse_equation (n0 : Float) (n : Float) (t : Int)
  (h1 : n0 > 0)
  (h2 : n > 0) 
  (h3 : n < n0)
  (h4 : t > 0) :
  let hl := half_life n0 n t
  n = n0 * (Float.pow 0.5 (Float.ofInt t / hl)) := sorry 

theorem half_life_exact_halving (n0 : Float) (num_halvings : Int)
  (h1 : n0 > 0)
  (h2 : num_halvings > 0) :
  let n := n0 * (Float.pow 0.5 (Float.ofInt num_halvings))
  half_life n0 n num_halvings = 1.0 := sorry
-- </vc-theorems>