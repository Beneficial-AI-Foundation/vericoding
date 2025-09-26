import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def polysub {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) : Id (Vector Float (max n m)) :=
  pure <|
    Vector.ofFn (fun i : Fin (max n m) =>
      if h1 : i.val < n ∧ i.val < m then
        c1.get ⟨i.val, h1.1⟩ - c2.get ⟨i.val, h1.2⟩
      else if h2 : i.val < n ∧ i.val ≥ m then
        c1.get ⟨i.val, h2.1⟩
      else if h3 : i.val ≥ n ∧ i.val < m then
        -c2.get ⟨i.val, h3.2⟩
      else
        (0 : Float)
    )
-- </vc-definitions>

-- <vc-theorems>
theorem polysub_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) :
    ⦃⌜True⌝⦄
    polysub c1 c2
    ⦃⇓result => ⌜∀ i : Fin (max n m),
        result.get i = 
          if h1 : i.val < n ∧ i.val < m then
            c1.get ⟨i.val, h1.1⟩ - c2.get ⟨i.val, h1.2⟩
          else if h2 : i.val < n ∧ i.val ≥ m then
            c1.get ⟨i.val, h2.1⟩
          else if h3 : i.val ≥ n ∧ i.val < m then
            -c2.get ⟨i.val, h3.2⟩
          else
            0⌝⦄ := by
  simpa [polysub] using
    (by
      intro _
      intro i
      simp
    )
-- </vc-theorems>
