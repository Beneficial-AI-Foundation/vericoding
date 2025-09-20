-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def poly_derivative (p : List Int) : List Int :=
  sorry

def scaleList (k : Int) (xs : List Int) : List Int :=
  sorry

def zeroList (n : Nat) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem derivative_length {p : List Int} (h : p ≠ []) :
  (poly_derivative p).length = p.length - 1 :=
sorry

theorem derivative_constant {p : List Int} (h : p.length = 1) :
  poly_derivative p = [] :=
sorry

theorem derivative_linear {p : List Int} (h : p.length ≥ 2) :
  (poly_derivative p).get! 0 = p.get! 1 :=
sorry
-- </vc-theorems>