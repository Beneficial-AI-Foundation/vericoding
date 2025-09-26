import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def vstack {n : Nat} (a b : Vector Float n) : Id (Vector (Vector Float n) 2) :=
  Pure.pure ⟨#[a, b], by simp⟩
-- </vc-definitions>

-- <vc-theorems>
theorem vstack_spec {n : Nat} (a b : Vector Float n) :
    ⦃⌜True⌝⦄
    vstack a b
    ⦃⇓result => ⌜(∀ j : Fin n, (result.get 0).get j = a.get j) ∧
                 (∀ j : Fin n, (result.get 1).get j = b.get j)⌝⦄ := by
  unfold vstack
  unfold Triple
  simp [pure]
  constructor
  · intro j
    simp [Vector.get]
    rfl
  · intro j
    simp [Vector.get]
    rfl
-- </vc-theorems>
