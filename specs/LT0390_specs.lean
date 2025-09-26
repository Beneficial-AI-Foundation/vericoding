-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chebmul {m n : Nat} (c1 : Vector Float m) (c2 : Vector Float n) 
    (hm : m > 0) (hn : n > 0) : Id (Vector Float (m + n - 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chebmul_spec {m n : Nat} (c1 : Vector Float m) (c2 : Vector Float n) 
    (hm : m > 0) (hn : n > 0) :
    ⦃⌜m > 0 ∧ n > 0⌝⦄
    chebmul c1 c2 hm hn
    ⦃⇓result => ⌜-- The result vector has the correct length
                result.toList.length = m + n - 1 ∧
                -- Example property: multiplying by the constant polynomial [a] scales all coefficients
                (∀ a : Float, n = 1 → c2.get ⟨0, sorry⟩ = a → 
                  ∀ i : Fin m, result.get ⟨i.val, sorry⟩ = a * c1.get i) ∧
                -- Another example: multiplying [1,0,...] (T_0) by any polynomial preserves it
                (m = 1 → c1.get ⟨0, sorry⟩ = 1 → 
                  ∀ j : Fin n, result.get ⟨j.val, sorry⟩ = c2.get j) ∧
                -- Special case: multiplying two linear polynomials [a,b] * [c,d]
                -- Result should be [ac + bd/2, ad + bc, bd/2]
                (m = 2 ∧ n = 2 → 
                  let a := c1.get ⟨0, sorry⟩
                  let b := c1.get ⟨1, sorry⟩
                  let c := c2.get ⟨0, sorry⟩
                  let d := c2.get ⟨1, sorry⟩
                  result.get ⟨0, sorry⟩ = a * c + b * d / 2 ∧
                  result.get ⟨1, sorry⟩ = a * d + b * c ∧
                  result.get ⟨2, sorry⟩ = b * d / 2) ∧
                -- Verify the example from documentation: [1,2,3] * [3,2,1]
                (m = 3 ∧ n = 3 → 
                  c1.get ⟨0, sorry⟩ = 1 ∧ c1.get ⟨1, sorry⟩ = 2 ∧ c1.get ⟨2, sorry⟩ = 3 →
                  c2.get ⟨0, sorry⟩ = 3 ∧ c2.get ⟨1, sorry⟩ = 2 ∧ c2.get ⟨2, sorry⟩ = 1 →
                  result.get ⟨0, sorry⟩ = 6.5 ∧
                  result.get ⟨1, sorry⟩ = 12 ∧
                  result.get ⟨2, sorry⟩ = 12 ∧
                  result.get ⟨3, sorry⟩ = 4 ∧
                  result.get ⟨4, sorry⟩ = 1.5)⌝⦄ := by
  sorry
-- </vc-theorems>