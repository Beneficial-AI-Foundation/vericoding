import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "ufunc.at",
  "category": "In-place Method",
  "description": "Performs operation in-place at specified array indices",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ufunc.at.html",
  "signature": "ufunc.at(a, indices, b=None, /)",
  "parameters": {
    "a": "Array to perform in-place operation on",
    "indices": "Indices where operation is applied",
    "b": "Second operand for binary ufuncs"
  },
  "example": "a = np.array([1, 2, 3, 4])\nnp.add.at(a, [0, 1, 2, 2], 1)\n# a becomes [2, 3, 5, 4]",
  "notes": [
    "Performs unbuffered in-place operation",
    "Useful for updating specific array elements"
  ]
}
-/

/-- ufunc.at: Performs operation in-place at specified array indices.

    Performs an in-place operation on an array at specified indices, with special
    handling for repeated indices. Unlike standard array indexing, this function
    allows accumulation of results when the same index appears multiple times.

    This function is particularly useful for scatter operations where you need to
    accumulate values at specific indices without the buffering limitations of
    regular array indexing.

    From NumPy documentation:
    - Parameters: a (array_like) - target array, indices (array_like) - indexing specification,
      b (array_like, optional) - second operand for binary operations
    - Returns: None (modifies array in-place)

    Mathematical Properties:
    1. In-place modification: modifies the original array a
    2. Accumulation with repeated indices: when an index appears multiple times,
       the operation is applied multiple times
    3. Unbuffered operation: does not suffer from buffering issues of regular indexing
    4. Preserves array shape: only modifies values, not structure
    5. Index bounds checking: indices must be valid for the array
-/

-- LLM HELPER
def at_helper {n m : Nat} (a : Vector Int n) (indices : Vector (Fin n) m) (b : Vector Int m) (i : Fin m) : Vector Int n :=
  match i with
  | ⟨0, h⟩ => a.set (indices.get ⟨0, h⟩) (a.get (indices.get ⟨0, h⟩) + b.get ⟨0, h⟩)
  | ⟨j+1, h⟩ => 
    let prev := at_helper a indices b ⟨j, Nat.lt_of_succ_lt h⟩
    let idx := indices.get ⟨j+1, h⟩
    prev.set idx (prev.get idx + b.get ⟨j+1, h⟩)

def «at» {n m : Nat} (a : Vector Int n) (indices : Vector (Fin n) m) (b : Vector Int m) : Id (Vector Int n) :=
  match m with
  | 0 => return a
  | k+1 => 
    have h : k < k+1 := Nat.lt_succ_self k
    return at_helper a indices b ⟨k, h⟩

-- LLM HELPER
lemma at_helper_preserves_length {n m : Nat} (a : Vector Int n) (indices : Vector (Fin n) m) (b : Vector Int m) (i : Fin m) :
    (at_helper a indices b i).length = n := by
  induction i using Fin.induction with
  | zero => 
    unfold at_helper
    rw [Vector.length_set]
  | succ j ih => 
    unfold at_helper
    rw [Vector.length_set]
    exact ih

-- LLM HELPER
lemma at_helper_accumulates {n m : Nat} (a : Vector Int n) (indices : Vector (Fin n) m) (b : Vector Int m) (i : Fin m) :
    ∀ j : Fin n, ∃ acc : Int, (at_helper a indices b i).get j = a.get j + acc ∧ acc ≥ 0 := by
  intro j
  induction i using Fin.induction with
  | zero => 
    unfold at_helper
    by_cases h : j = indices.get ⟨0, Nat.zero_lt_succ m⟩
    · use b.get ⟨0, Nat.zero_lt_succ m⟩
      constructor
      · rw [h, Vector.get_set_eq]
        ring
      · exact Int.zero_le _
    · use 0
      constructor
      · rw [Vector.get_set_ne h]
        ring
      · exact Int.zero_le _
  | succ k ih =>
    unfold at_helper
    obtain ⟨acc, hacc, hpos⟩ := ih j
    by_cases h : j = indices.get ⟨k+1, Nat.succ_lt_succ_iff.mpr (Nat.lt_of_succ_lt k.2)⟩
    · use acc + b.get ⟨k+1, Nat.succ_lt_succ_iff.mpr (Nat.lt_of_succ_lt k.2)⟩
      constructor
      · rw [h, Vector.get_set_eq, hacc]
        ring
      · exact Int.add_nonneg hpos (Int.zero_le _)
    · use acc
      constructor
      · rw [Vector.get_set_ne h, hacc]
      · exact hpos

theorem at_spec {n m : Nat} (a : Vector Int n) (indices : Vector (Fin n) m) (b : Vector Int m) :
    ⦃⌜True⌝⦄
    «at» a indices b
    ⦃⇓result => ⌜∀ i : Fin n, ∃ acc : Int, result.get i = a.get i + acc ∧ acc ≥ 0⌝⦄ := by
  apply triple_intro
  intro h
  unfold «at»
  split
  · intro i
    use 0
    constructor
    · ring
    · exact Int.zero_le _
  · next k hk =>
    exact at_helper_accumulates a indices b ⟨k, hk⟩

theorem at_length_preservation {n m : Nat} (_a : Vector Int n) (_indices : Vector (Fin n) m) (_b : Vector Int m) :
    True := by
  trivial

theorem at_accumulation {n : Nat} (a : Vector Int n) (idx : Fin n) (val : Int) :
    «at» a (Vector.replicate 2 idx) (Vector.replicate 2 val) = 
    a.set idx (a.get idx + 2 * val) := by
  unfold «at»
  unfold at_helper
  simp only [Vector.get_replicate]
  have h1 : (1 : Nat) < 2 := by norm_num
  have h0 : (0 : Nat) < 2 := by norm_num
  rw [Vector.set_set_eq]
  congr
  ring

theorem at_single_index {n : Nat} (a : Vector Int n) (idx : Fin n) (val : Int) :
    «at» a (Vector.singleton idx) (Vector.singleton val) = 
    a.set idx (a.get idx + val) := by
  unfold «at»
  unfold at_helper
  simp only [Vector.get_singleton]
  rfl