-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def RealFunction := Float → Float

def riemann_trapezoidal (f : RealFunction) (n : Nat) (a b : Float) : Float := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem riemann_trapezoidal_constant_function 
    (n : Nat) (a b : Float) (h : a ≤ b) (const : Float) :
    let f := fun x => const
    (riemann_trapezoidal f n a b - (const * (b - a))).abs < 0.1 :=
  sorry

theorem riemann_trapezoidal_linear_function (n : Nat) :
    let f := fun x => x
    (riemann_trapezoidal f n 0 1 - 0.5).abs < 0.1 :=
  sorry
-- </vc-theorems>