-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def zeros_like {n : Nat} {T : Type} [Zero T] (a : Vector T n) : Id (Vector T n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zeros_like_spec {n : Nat} {T : Type} [Zero T] [Add T] (a : Vector T n) :
    ⦃⌜True⌝⦄
    zeros_like a
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = 0) ∧
                 (∀ v : Vector T n, ∀ i : Fin n, 
                   (result.get i + v.get i = v.get i) ∧ 
                   (v.get i + result.get i = v.get i))⌝⦄ := by
  sorry
-- </vc-theorems>