-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Legendre polynomial of degree n evaluated at x -/
def legendre_poly : Nat → Float → Float := fun n x => sorry

/-- Least squares fit of Legendre series to data.
    
    Returns the coefficients of a Legendre series of degree `deg` that is the
    least squares fit to the data values `y` given at points `x`. The fitted
    polynomial is in the form:
    
    p(x) = c_0 + c_1 * L_1(x) + ... + c_n * L_n(x)
    
    where `n` is `deg` and L_i are Legendre polynomials.
-/
def legfit {m : Nat} (x : Vector Float m) (y : Vector Float m) (deg : Nat) 
    (h_nonempty : m > 0) (h_deg_bound : deg < m) : Id (Vector Float (deg + 1)) :=
  sorry

/-- Specification: legfit computes coefficients that minimize least squares error
    
    The returned coefficients define a Legendre polynomial that minimizes the
    sum of squared errors between the fitted polynomial and the data points.
    The degree of the resulting polynomial is exactly `deg`.
-/
theorem legfit_spec {m : Nat} (x : Vector Float m) (y : Vector Float m) (deg : Nat) 
    (h_nonempty : m > 0) (h_deg_bound : deg < m) :
    ⦃⌜m > 0 ∧ deg < m⌝⦄
    legfit x y deg h_nonempty h_deg_bound
    ⦃⇓coeff => ⌜coeff.toArray.size = deg + 1 ∧ 
                 (∀ other_coeff : Vector Float (deg + 1), 
                   let fitted_vals := fun i : Fin m => 
                     (List.range (deg + 1)).foldl (fun acc j => 
                       acc + coeff.get ⟨j, by sorry⟩ * (legendre_poly j (x.get i))) 0
                   let other_vals := fun i : Fin m => 
                     (List.range (deg + 1)).foldl (fun acc j => 
                       acc + other_coeff.get ⟨j, by sorry⟩ * (legendre_poly j (x.get i))) 0
                   let error_fitted := (List.range m).foldl (fun acc i => 
                     acc + (y.get ⟨i, by sorry⟩ - fitted_vals ⟨i, by sorry⟩)^2) 0
                   let error_other := (List.range m).foldl (fun acc i => 
                     acc + (y.get ⟨i, by sorry⟩ - other_vals ⟨i, by sorry⟩)^2) 0
                   error_fitted ≤ error_other)⌝⦄ := by
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>