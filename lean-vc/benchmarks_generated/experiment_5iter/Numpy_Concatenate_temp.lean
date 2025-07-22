import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.concatenate: Join a sequence of arrays along an existing axis.

    For 1D arrays, concatenate joins arrays end-to-end. This is the
    simplest form of concatenation - appending one array after another.
    The result has length equal to the sum of input lengths.

    This version handles concatenating two 1D arrays. The general version
    would handle a list of arrays.
-/
def numpy_concatenate {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
    Id (Vector Float (n + m)) :=
  pure ⟨(a.toList ++ b.toList).toArray, by simp [List.length_append]⟩

-- LLM HELPER
lemma list_getElem_append_right {α : Type*} (l₁ l₂ : List α) (i : Nat) (h : l₁.length ≤ i) 
  (h' : i < l₁.length + l₂.length) (h'' : i - l₁.length < l₂.length) :
  (l₁ ++ l₂)[i]'h' = l₂[i - l₁.length]'h'' := by
  rw [List.getElem_append_right]
  exact h

/-- Specification: numpy.concatenate appends the second array after the first.

    Precondition: True (no special preconditions for basic concatenation)
    Postcondition: First n elements come from a, next m elements come from b
-/
theorem numpy_concatenate_spec {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
    ⦃⌜True⌝⦄
    numpy_concatenate a b
    ⦃⇓result => ⌜(∀ i : Fin n, result.get (i.castAdd m) = a.get i) ∧
                (∀ j : Fin m, result.get (j.natAdd n) = b.get j)⌝⦄ := by
  unfold numpy_concatenate
  simp
  intro h
  constructor
  · intro i
    simp [Vector.get]
    have h1 : i.val < n := i.isLt
    rw [List.getElem_append_left]
    simp [Vector.get]
  · intro j
    simp [Vector.get]
    have h1 : n ≤ j.val + n := Nat.le_add_left n j.val
    rw [list_getElem_append_right]
    · simp [Vector.get]
      congr
      omega
    · omega
    · omega
    · omega