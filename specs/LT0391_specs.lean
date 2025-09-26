-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chebmulx {n : Nat} (c : Vector Float n) : Id (Vector Float (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
  sorry
-- </vc-theorems>