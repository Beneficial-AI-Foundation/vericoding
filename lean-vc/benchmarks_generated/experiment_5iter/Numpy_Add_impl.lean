import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.add: Add arguments element-wise.

    Adds two vectors element-wise. If the vectors have the same shape,
    each element of the result is the sum of the corresponding elements
    from the input vectors.

    This is equivalent to x1 + x2 in terms of array broadcasting.
-/
def numpy_add {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  Id.pure (Vector.mk (List.zipWith (· + ·) x1.val x2.val) (by
    simp [List.length_zipWith]
    rw [x1.property, x2.property]
    exact Nat.min_self n))

-- LLM HELPER
lemma list_get_zipWith_add {α : Type*} [Add α] (l1 l2 : List α) (i : Nat) (h1 : i < l1.length) (h2 : i < l2.length) :
    (List.zipWith (· + ·) l1 l2).get ⟨i, by simp [List.length_zipWith]; exact Nat.lt_min_iff.mpr ⟨h1, h2⟩⟩ = 
    l1.get ⟨i, h1⟩ + l2.get ⟨i, h2⟩ := by
  simp [List.get_zipWith]

/-- Specification: numpy.add returns a vector where each element is the sum
    of the corresponding elements from x1 and x2.

    Precondition: True (no special preconditions for basic addition)
    Postcondition: For all indices i, result[i] = x1[i] + x2[i]
-/
theorem numpy_add_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_add x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x1.get i + x2.get i⌝⦄ := by
  unfold numpy_add
  simp [wp_pure]
  intro i
  simp [Vector.get]
  rw [list_get_zipWith_add]
  · rw [x1.property]
    exact i.2
  · rw [x2.property]
    exact i.2