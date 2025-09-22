-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solveTennis (n : Nat) (bounds : List Float) (ballPos : List Float) (velocities : List Float) 
  (chefPos : List Float) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dimensions_match (n : Nat) 
  (h1 : 0 < n) (h2 : n ≤ 10) 
  (bounds : List Float) 
  (hb : bounds.length = n)
  (ball_pos : List Float)
  (hbp : ball_pos.length = n) 
  (velocities : List Float)
  (hv : velocities.length = n)
  (chef_pos : List Float)
  (hc : chef_pos.length = n) :
  ∃ (t : Float), solveTennis n bounds ball_pos velocities chef_pos = t :=
  sorry

theorem same_position_zero_time
  (n : Nat)
  (h1 : 0 < n) (h2 : n ≤ 10)
  (bounds : List Float)
  (hb : bounds.length = n)
  (pos : List Float) 
  (hp : pos.length = n)
  (vel : List Float)
  (hv : vel.length = n) :
  Float.abs (solveTennis n bounds pos vel pos) < 1e-8 :=
  sorry
-- </vc-theorems>