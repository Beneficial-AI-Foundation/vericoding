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
def numpy_where {n : Nat} (condition : Vector Bool n) (x y : Vector Float n) : Id (Vector Float n) :=
  pure (Vector.ofFn (fun i => if condition.get i = true then x.get i else y.get i))
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_where_spec {n : Nat} (condition : Vector Bool n) (x y : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_where condition x y
    ⦃⇓result => ⌜∀ i : Fin n, 
      (condition.get i = true → result.get i = x.get i) ∧
      (condition.get i = false → result.get i = y.get i)⌝⦄ := by
  intro _
  simp [numpy_where]
  intro i
  constructor
  · intro h
    simp [Vector.get_ofFn, h]
  · intro h
    simp [Vector.get_ofFn, h]
-- </vc-theorems>
