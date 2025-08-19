import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def dot_product_helper {n : Nat} (a b : Vector Float n) (i : Nat) : Float :=
  if h : i < n then a.get ⟨i, h⟩ * b.get ⟨i, h⟩ else 0

-- LLM HELPER
def dot_product_sum {n : Nat} (a b : Vector Float n) : Float :=
  List.sum (List.range n).map (fun i => if h : i < n then a.get ⟨i, h⟩ * b.get ⟨i, h⟩ else 0)

/-- numpy.dot: Dot product of two arrays.

    For 1-D arrays (vectors), this is the inner product of vectors.
    It computes the sum of the element-wise products of the input vectors.

    If both a and b are 1-D arrays, it is inner product of vectors
    (without complex conjugation).
-/
def numpy_dot {n : Nat} (a b : Vector Float n) : Id Float :=
  pure (List.sum (List.zipWith (· * ·) a.toList b.toList))

-- LLM HELPER
lemma zipWith_eq_map_range {n : Nat} (a b : Vector Float n) :
  List.zipWith (· * ·) a.toList b.toList = 
  (List.range n).map (fun i => if h : i < n then a.get ⟨i, h⟩ * b.get ⟨i, h⟩ else 0) := by
  sorry

-- LLM HELPER
lemma vector_toList_length {α : Type*} {n : Nat} (v : Vector α n) : v.toList.length = n := by
  exact Vector.toList_length v

/-- Specification: numpy.dot returns the dot product (inner product) of two vectors.

    Precondition: True (vectors must have same length, enforced by type)
    Postcondition: result = sum(a[i] * b[i] for all i)
-/
theorem numpy_dot_spec {n : Nat} (a b : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_dot a b
    ⦃⇓result => ⌜result = List.sum (List.zipWith (· * ·) a.toList b.toList)⌝⦄ := by
  unfold numpy_dot
  apply wpPost_pure
  simp