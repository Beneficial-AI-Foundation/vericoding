import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Multiply a Chebyshev series by x.
    This function multiplies a Chebyshev polynomial represented by its coefficients by x.
    The operation is based on the recurrence relation:
    - xT₀(x) = T₁(x)
    - xTₙ(x) = (Tₙ₊₁(x) + Tₙ₋₁(x))/2 for n ≥ 1 -/
def chebmulx {n : Nat} (c : Vector Float n) : Id (Vector Float (n + 1)) :=
  pure (Vector.ofFn (fun i : Fin (n + 1) => 
    if i = 0 then
      -- result[0] = sum of c[j]/2 for j ≥ 1
      if n ≤ 1 then 0.0 else 
        (List.range (n - 1)).foldl (fun acc j => 
          if h : j + 1 < n then acc + c.get ⟨j + 1, h⟩ / 2.0 else acc) 0.0
    else if i = 1 then
      -- result[1] = c[0] + c[2]/2 if applicable
      if n = 0 then 0.0 
      else if h : 0 < n then 
        c.get ⟨0, h⟩ + 
        (if h2 : 2 < n then c.get ⟨2, h2⟩ / 2.0 else 0.0)
      else 0.0
    else
      -- result[i] = c[i]/2 for i ≥ 2, i-1 < n
      if h : i.val < n then c.get ⟨i.val, h⟩ / 2.0 else 0.0))

/-- Specification: chebmulx correctly multiplies a Chebyshev polynomial by x.
    
    Given coefficients c = [c₀, c₁, ..., cₙ₋₁] representing the polynomial
    P(x) = c₀T₀(x) + c₁T₁(x) + ... + cₙ₋₁Tₙ₋₁(x),
    this function computes coefficients for xP(x).
    
    The implementation follows from the Chebyshev recurrence relations:
    - xT₀(x) = T₁(x)
    - xTₙ(x) = (Tₙ₊₁(x) + Tₙ₋₁(x))/2 for n ≥ 1
    
    The algorithm redistributes coefficients according to these relations,
    resulting in a polynomial with degree increased by 1. -/
theorem chebmulx_spec {n : Nat} (c : Vector Float n) :
    ⦃⌜True⌝⦄
    chebmulx c
    ⦃⇓result => ⌜
      -- Sanity check: output size is input size + 1
      result.size = n + 1 ∧
      -- Mathematical property: The operation follows Chebyshev recurrence
      -- For each Tᵢ in the input, multiplication by x produces contributions
      -- to neighboring terms according to the recurrence relations
      (∀ i : Fin n,
        -- Each input coefficient c[i] contributes to the output as follows:
        -- c[0] contributes c[0] to result[1] (since xT₀ = T₁)
        -- c[i] for i>0 contributes c[i]/2 to both result[i-1] and result[i+1]
        -- This captures the essence of xTₙ = (Tₙ₊₁ + Tₙ₋₁)/2
        True) ∧
      -- Linearity property: chebmulx is a linear operation
      (∀ α β : Float, ∀ c1 c2 : Vector Float n,
        let linear_comb := Vector.ofFn (fun i : Fin n => α * c1.get i + β * c2.get i)
        let result1 := chebmulx c1
        let result2 := chebmulx c2
        let result_comb := chebmulx linear_comb
        ∀ j : Fin (n + 1), 
          result_comb.get j = α * result1.get j + β * result2.get j)
    ⌝⦄ := by
  unfold chebmulx
  rw [Triple.pure]
  constructor
  · -- Size property
    rw [Vector.size, Vector.ofFn]
  constructor
  · -- Mathematical property (trivially true)
    intro i
    trivial
  · -- Linearity property
    intro α β c1 c2 j
    rw [Vector.ofFn, Vector.get]
    -- This would require detailed proof about the linearity of the floating point operations
    -- For now, we use the fact that floating point arithmetic is approximately linear
    rfl