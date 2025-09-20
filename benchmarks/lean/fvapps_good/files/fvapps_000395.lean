-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def new21Game (N K W : Nat) : Float := sorry

def approx_equal (a b epsilon : Float) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem new21Game_bounds (N K W : Nat) (h : K ≤ N + 1) :
  let result := new21Game N K W
  0 ≤ result ∧ result ≤ 1 := sorry
-- </vc-theorems>