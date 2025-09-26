import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem vector_get_ofFn {α : Type _} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  simp

-- LLM HELPER
@[simp] theorem vector_get_ofFn2 {α : Type _} {n m : Nat}
    (f : (i : Fin n) → Fin m → α) (i : Fin n) (j : Fin m) :
    ((Vector.ofFn (fun i => Vector.ofFn (f i))).get i).get j = f i j := by
  simp
-- </vc-helpers>

-- <vc-definitions>
def tri (N M : Nat) (k : Int) : Id (Vector (Vector Float M) N) :=
  pure <|
    Vector.ofFn (fun i : Fin N =>
      Vector.ofFn (fun j : Fin M =>
        if (j.val : Int) ≤ (i.val : Int) + k then (1.0 : Float) else (0.0 : Float)))
-- </vc-definitions>

-- <vc-theorems>
theorem tri_spec (N M : Nat) (k : Int) :
    ⦃⌜True⌝⦄
    tri N M k
    ⦃⇓result => ⌜∀ (i : Fin N) (j : Fin M), 
                  (result.get i).get j = if (j.val : Int) ≤ (i.val : Int) + k then 1.0 else 0.0⌝⦄ := by
  classical
  intro _ i j
  simp [tri]
-- </vc-theorems>
