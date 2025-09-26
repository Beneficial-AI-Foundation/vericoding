-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chebcompanion {n : Nat} (c : Vector Float (n + 2)) : Id (Vector (Vector Float (n + 1)) (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chebcompanion_spec {n : Nat} (c : Vector Float (n + 2)) :
    ⦃⌜True⌝⦄
    chebcompanion c
    ⦃⇓mat => ⌜-- The resulting matrix has specific structure for Chebyshev companion matrices
              -- Superdiagonal elements (above main diagonal)
              (∀ i : Fin n, (mat.get i.castSucc).get i.succ = 0.5) ∧
              -- Special case for first superdiagonal element
              (n > 0 → (mat.get 0).get 1 = Float.sqrt 0.5) ∧
              -- Subdiagonal elements (below main diagonal)  
              (∀ i : Fin n, (mat.get i.succ).get i.castSucc = 0.5) ∧
              -- Special case for first subdiagonal element
              (n > 0 → (mat.get 1).get 0 = Float.sqrt 0.5) ∧
              -- Last column contains scaled coefficient ratios
              (∀ i : Fin (n + 1), 
                ∃ adjustment : Float,
                adjustment = (c.get i.castSucc / c.get (Fin.last (n + 1))) * 0.5 ∧
                (mat.get i).get (Fin.last n) = 
                  (if h : i.val < n then
                     (if i = 0 then -Float.sqrt 0.5 else -0.5) - adjustment
                   else -adjustment))⌝⦄ := by
  sorry
-- </vc-theorems>