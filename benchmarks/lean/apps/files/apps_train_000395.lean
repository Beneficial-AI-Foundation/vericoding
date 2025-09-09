-- <vc-helpers>
-- </vc-helpers>

def new21Game (N K W : Nat) : Float := sorry

def approx_equal (a b epsilon : Float) : Bool := sorry

theorem new21Game_bounds (N K W : Nat) (h : K ≤ N + 1) :
  let result := new21Game N K W
  0 ≤ result ∧ result ≤ 1 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible