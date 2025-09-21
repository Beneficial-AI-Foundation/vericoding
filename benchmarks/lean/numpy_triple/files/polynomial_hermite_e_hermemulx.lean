-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermemulx {n : Nat} (c : Vector Float n) : Id (Vector Float (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermemulx_spec {n : Nat} (c : Vector Float n) :
    ⦃⌜True⌝⦄
    hermemulx c
    ⦃⇓result => ⌜
      -- Coefficient at position 0 is always 0 (no constant term in x*polynomial)
      result.get ⟨0, by simp⟩ = 0 ∧
      -- For n > 0: coefficient at position 1 comes from c[0] plus recursive contributions  
      (∀ (h : n > 0), result.get ⟨1, sorry⟩ = c.get ⟨0, h⟩ + 
        (if n > 1 then (c.get ⟨1, sorry⟩) * (1 : Float) else 0)) ∧
      -- For i ≥ 1: result[i+1] gets c[i] (coefficient shift up)
      (∀ i : Fin n, i.val ≥ 1 → result.get ⟨i.val + 1, sorry⟩ = c.get i)
    ⌝⦄ := by
  sorry
-- </vc-theorems>