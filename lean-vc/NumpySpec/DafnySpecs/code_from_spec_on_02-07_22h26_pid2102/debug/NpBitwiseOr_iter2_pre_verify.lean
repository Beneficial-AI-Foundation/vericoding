/-
# NumPy Bitwise Or Specification

Port of np_bitwise_or.dfy to Lean 4
-/

namespace DafnySpecs.NpBitwiseOr

/-- Element-wise bitwise OR of two vectors -/
def bitwiseOr {n : Nat} (a b : Vector Nat n) : Vector Nat n := 
  Vector.ofFn (fun i => a[i] ||| b[i])

/-- LLM HELPER -/
lemma Vector.toList_ofFn_length {α : Type*} {n : Nat} (f : Fin n → α) :
  (Vector.ofFn f).toList.length = n := by
  rw [Vector.ofFn_toList]
  simp [List.length_ofFn]

/-- LLM HELPER -/
lemma Vector.get_ofFn {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f)[i] = f i := by
  rw [Vector.get_ofFn]

/-- Specification: The result has the same length as inputs -/
theorem bitwiseOr_length {n : Nat} (a b : Vector Nat n) :
  (bitwiseOr a b).toList.length = n := by
  unfold bitwiseOr
  exact Vector.toList_ofFn_length _

/-- Specification: Each element is the bitwise OR of corresponding input elements -/
theorem bitwiseOr_spec {n : Nat} (a b : Vector Nat n) :
  ∀ i : Fin n, (bitwiseOr a b)[i] = a[i] ||| b[i] := by
  intro i
  unfold bitwiseOr
  exact Vector.get_ofFn _ i

end DafnySpecs.NpBitwiseOr