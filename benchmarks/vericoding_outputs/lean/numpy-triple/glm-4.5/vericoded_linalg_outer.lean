import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Helper function to create a vector by applying a function to each index
def vectorOfFn {n : Nat} {α : Type} (f : Fin n → α) : Vector α n :=
  Vector.ofFn f

-- LLM HELPER: Helper function to create a matrix (vector of vectors) 
def matrixOfFn {m n : Nat} {α : Type} (f : Fin m → Fin n → α) : Vector (Vector α n) m :=
  vectorOfFn fun i => vectorOfFn (f i)

-- LLM HELPER: Lemma about Vector.get and Vector.ofFn
theorem vectorOfFn_get {n : Nat} {α : Type} (f : Fin n → α) (i : Fin n) :
    (vectorOfFn f).get i = f i := by
  simp [vectorOfFn, Vector.ofFn]
-- </vc-helpers>

-- <vc-definitions>
def outer {m n : Nat} [Mul α] (a : Vector α m) (b : Vector α n) : Id (Vector (Vector α n) m) :=
  pure $ matrixOfFn fun i j => a.get i * b.get j
-- </vc-definitions>

-- <vc-theorems>
theorem outer_spec {m n : Nat} [Mul α] (a : Vector α m) (b : Vector α n) :
    ⦃⌜True⌝⦄
    outer a b
    ⦃⇓result => ⌜
      -- Core property: Each matrix element is the product of corresponding vector elements
      -- This captures the fundamental definition of outer product: (a ⊗ b)[i,j] = a[i] * b[j]
      ∀ (i : Fin m) (j : Fin n), (result.get i).get j = a.get i * b.get j
    ⌝⦄ := by
  unfold outer
  simp [matrixOfFn, vectorOfFn]
  intro i j
  simp [vectorOfFn_get]
-- </vc-theorems>
