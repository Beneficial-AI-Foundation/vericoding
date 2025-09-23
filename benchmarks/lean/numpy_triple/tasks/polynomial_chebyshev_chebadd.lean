-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chebadd {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) : Id (Vector Float (max n m)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chebadd_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) :
    ⦃⌜True⌝⦄
    chebadd c1 c2
    ⦃⇓result => ⌜(∀ i : Fin (max n m), 
        result.get i = 
          if h1 : i.val < n then
            if h2 : i.val < m then
              c1.get ⟨i.val, h1⟩ + c2.get ⟨i.val, h2⟩
            else
              c1.get ⟨i.val, h1⟩
          else
            if h2 : i.val < m then
              c2.get ⟨i.val, h2⟩
            else
              0) ∧ 
      -- Sanity check: result preserves non-zero coefficients
      (∀ i : Fin n, c1.get i ≠ 0 → ∃ j : Fin (max n m), j.val = i.val ∧ 
        (if h2 : i.val < m then result.get j = c1.get i + c2.get ⟨i.val, h2⟩ else result.get j = c1.get i)) ∧
      (∀ i : Fin m, c2.get i ≠ 0 → ∃ j : Fin (max n m), j.val = i.val ∧ 
        (if h1 : i.val < n then result.get j = c1.get ⟨i.val, h1⟩ + c2.get i else result.get j = c2.get i))
    ⌝⦄ := by
  sorry
-- </vc-theorems>