-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def zeros (n : Nat) (α : Type) [Zero α] : Id (Vector α n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zeros_spec (n : Nat) (α : Type) [Zero α] [Add α] [Mul α] :
    ⦃⌜True⌝⦄
    zeros n α
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = 0) ∧
                 (∀ v : Vector α n, ∀ i : Fin n, 
                   (result.get i + v.get i = v.get i) ∧ 
                   (v.get i + result.get i = v.get i)) ∧
                 (∀ scalar : α, ∀ i : Fin n,
                   scalar * result.get i = 0) ∧
                 (∀ v : Vector α n, ∀ i : Fin n,
                   result.get i * v.get i = 0) ∧
                 (n > 0 → result.get ⟨0, sorry⟩ = 0)⌝⦄ := by
  sorry
-- </vc-theorems>