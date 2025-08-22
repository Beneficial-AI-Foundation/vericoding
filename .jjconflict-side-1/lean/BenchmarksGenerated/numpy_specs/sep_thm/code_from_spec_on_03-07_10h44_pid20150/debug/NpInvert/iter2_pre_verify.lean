/-
# NumPy Invert Specification

Port of np_invert.dfy to Lean 4
-/

namespace DafnySpecs.NpInvert

/-- Element-wise bitwise NOT (invert) of a vector with specified bit width -/
def invert {n : Nat} (bitWidth : Nat) (a : Vector Nat n) : Vector Nat n := 
  Vector.map (fun x => (2^bitWidth - 1) - x) a

/-- Specification: The result has the same length as input -/
theorem invert_length {n : Nat} (bitWidth : Nat) (a : Vector Nat n) :
  (invert bitWidth a).toList.length = n := by
  simp [invert, Vector.toList_map]

/-- Specification: Each element is the bitwise NOT of the corresponding input element 
    within the specified bit width (i.e., flips all bits up to bitWidth) -/
theorem invert_spec {n : Nat} (bitWidth : Nat) (a : Vector Nat n) :
  ∀ i : Fin n, (invert bitWidth a)[i] = (2^bitWidth - 1) - a[i] := by
  intro i
  simp [invert]
  rw [Vector.get_map]

end DafnySpecs.NpInvert