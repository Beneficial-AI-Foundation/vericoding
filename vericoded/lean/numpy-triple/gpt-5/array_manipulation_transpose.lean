import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
universe u

/-- Transpose a matrix represented as a vector of row-vectors. -/
def vectorTranspose {α : Type u} {rows cols : Nat}
    (a : Vector (Vector α cols) rows) :
    Vector (Vector α rows) cols :=
  Vector.ofFn (fun j => Vector.ofFn (fun i => (a.get i).get j))

@[simp] theorem vectorTranspose_get_get {α : Type u}
    {rows cols : Nat} (a : Vector (Vector α cols) rows)
    (j : Fin cols) (i : Fin rows) :
    ((vectorTranspose a).get j).get i = (a.get i).get j := by
  simp [vectorTranspose]

-- </vc-helpers>

-- <vc-definitions>
def numpy_transpose {rows cols : Nat} (a : Vector (Vector Float cols) rows) : 
    Id (Vector (Vector Float rows) cols) :=
  pure (vectorTranspose a)
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_transpose_spec {rows cols : Nat} (a : Vector (Vector Float cols) rows) :
    ⦃⌜True⌝⦄
    numpy_transpose a
    ⦃⇓result => ⌜∀ (i : Fin rows) (j : Fin cols), 
                  (result.get j).get i = (a.get i).get j⌝⦄ := by
  simpa [numpy_transpose, vectorTranspose] using
    (by
      intro (_h : True)
      intro i j
      simp [vectorTranspose]
    )
-- </vc-theorems>
