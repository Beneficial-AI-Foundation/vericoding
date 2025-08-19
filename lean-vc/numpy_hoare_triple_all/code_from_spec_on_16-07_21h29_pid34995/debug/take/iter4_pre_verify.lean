import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Take elements from a source array at specified indices.
    Given a source array 'arr' and a vector of indices 'indices',
    returns a new array containing the elements from 'arr' at the positions
    specified by 'indices'. The indices must be valid positions in the source array.
    
    This is a simplified 1D version of numpy.take with 'raise' mode,
    where all indices must be valid (in range [0, n-1]). -/
def take {n m : Nat} (arr : Vector Float n) (indices : Vector (Fin n) m) : Id (Vector Float m) :=
  Vector.ofFn (fun i => arr.get (indices.get i))

-- LLM HELPER
lemma Vector.get_ofFn {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  rfl

-- LLM HELPER
lemma Vector.get_elem_eq_some {α : Type*} {n : Nat} (v : Vector α n) (i : Fin n) :
    v[i]? = some (v.get i) := by
  simp [Vector.get?_eq_get]

/-- Specification: take extracts elements from a source array at specified indices.
    
    Mathematical properties:
    1. The result has the same length as the indices array
    2. For each position i in the result, result[i] = arr[indices[i]]
    3. All indices must be valid (enforced by Fin type)
    4. The order of elements in the result follows the order of indices
    5. The same index can appear multiple times, resulting in duplicated elements
    
    The function implements: result[i] = arr[indices.get i]?
    
    This captures the core behavior of numpy.take in 'raise' mode where indices
    must be in valid range. The use of Fin type ensures type safety and eliminates
    the need for runtime bounds checking. The result preserves the element type
    of the source array. -/
theorem take_spec {n m : Nat} (arr : Vector Float n) (indices : Vector (Fin n) m) :
    ⦃⌜True⌝⦄
    take arr indices
    ⦃⇓result => ⌜∀ i : Fin m, result.get i = arr[indices.get i]?⌝⦄ := by
  simp [take]
  simp [Vector.get_ofFn]
  simp [Vector.get_elem_eq_some]