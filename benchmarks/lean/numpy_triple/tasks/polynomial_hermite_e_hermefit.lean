-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Helper function for Hermite_e polynomial evaluation (probabilist's Hermite polynomials)
    He_n(x) = (-1)^n * exp(x^2/2) * d^n/dx^n * exp(-x^2/2) -/
def hermiteE : Nat → Float → Float
| 0, _ => 1
| 1, x => x  
| n + 2, x => 
    let coeff := Float.ofNat (n + 1)
    x * hermiteE (n + 1) x - coeff * hermiteE n x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermefit {m : Nat} (x : Vector Float m) (y : Vector Float m) (deg : Nat) 
    (h_size : deg + 1 ≤ m) (h_nonempty : m > 0) : Id (Vector Float (deg + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermefit_spec {m : Nat} (x : Vector Float m) (y : Vector Float m) (deg : Nat)
    (h_size : deg + 1 ≤ m) (h_nonempty : m > 0) :
    ⦃⌜deg + 1 ≤ m ∧ m > 0⌝⦄
    hermefit x y deg h_size h_nonempty
    ⦃⇓coef => ⌜
      -- Sanity check: coefficients are finite
      (∀ i : Fin (deg + 1), 
        let ci := coef.get i
        ¬ci.isNaN ∧ ¬ci.isInf) ∧
      -- Basic property: the result has the correct size
      coef.size = deg + 1 ∧
      -- Least squares property: the coefficients minimize the sum of squared residuals
      -- For any other coefficient vector c of the same degree,
      -- the sum of squared residuals using coef is ≤ that using c
      (∀ c : Vector Float (deg + 1), 
        let residual_coef := (List.finRange m).map (fun i => 
          let xi := x.get i
          let yi := y.get i
          let pred := (List.finRange (deg + 1)).foldl (fun acc j => 
            acc + (coef.get j) * (hermiteE j.val xi)) 0
          (yi - pred) ^ 2)
        let residual_c := (List.finRange m).map (fun i => 
          let xi := x.get i
          let yi := y.get i
          let pred := (List.finRange (deg + 1)).foldl (fun acc j => 
            acc + (c.get j) * (hermiteE j.val xi)) 0
          (yi - pred) ^ 2)
        residual_coef.sum ≤ residual_c.sum) ∧
      -- Exact interpolation property: when we have exactly deg+1 points,
      -- the polynomial passes through all points exactly
      (deg + 1 = m → 
        ∀ i : Fin m, 
          let xi := x.get i
          let yi := y.get i
          let pred := (List.finRange (deg + 1)).foldl (fun acc j => 
            acc + (coef.get j) * (hermiteE j.val xi)) 0
          Float.abs (yi - pred) < 1e-10) ∧
      -- Orthogonality condition: the residuals are orthogonal to the basis functions
      -- This is a fundamental property of least squares solutions
      (∀ k : Fin (deg + 1), 
        let residuals := (List.finRange m).map (fun i => 
          let xi := x.get i
          let yi := y.get i
          let pred := (List.finRange (deg + 1)).foldl (fun acc j => 
            acc + (coef.get j) * (hermiteE j.val xi)) 0
          yi - pred)
        let basis_vals := (List.finRange m).map (fun i => 
          hermiteE k.val (x.get i))
        Float.abs ((residuals.zip basis_vals).map (fun p => p.1 * p.2)).sum < 1e-10)
    ⌝⦄ := by
  sorry
-- </vc-theorems>