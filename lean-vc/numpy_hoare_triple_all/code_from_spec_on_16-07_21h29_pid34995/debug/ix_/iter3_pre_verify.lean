import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
lemma zero_lt_one : (0 : Nat) < 1 := by norm_num

/-- Construct an open mesh from two 1-D sequences. 
    This simplified version handles the case of two input sequences,
    returning two 2D arrays that form an open mesh for indexing operations.
    The first array has shape (m, 1) containing values from the first sequence,
    and the second array has shape (1, n) containing values from the second sequence. -/
def ix_ {m n : Nat} (seq1 : Vector Int m) (seq2 : Vector Int n) : Id (Vector (Vector Int 1) m × Vector (Vector Int n) 1) :=
  let first := Vector.map (fun x => Vector.replicate 1 x) seq1
  let second := Vector.replicate 1 seq2
  pure (first, second)

/-- Specification: ix_ creates an open mesh from two sequences
    This comprehensive specification captures:
    1. The function takes two 1-D sequences of integers
    2. Returns a pair of 2D arrays (represented as vectors of vectors)
    3. First array has shape (m, 1) - m rows, 1 column
    4. Second array has shape (1, n) - 1 row, n columns
    5. First array contains values from seq1 repeated in column format
    6. Second array contains values from seq2 repeated in row format
    7. Together they form an open mesh for advanced indexing operations
    8. Each element of the first array's i-th row equals seq1[i]
    9. Each element of the second array's single row equals the corresponding seq2 element
    10. The mesh property: for any indices (i,j), the pair (first[i][0], second[0][j]) 
        represents a coordinate in the mesh grid -/
theorem ix_spec {m n : Nat} (seq1 : Vector Int m) (seq2 : Vector Int n) :
    ⦃⌜True⌝⦄
    ix_ seq1 seq2
    ⦃⇓result => ⌜-- First array has correct shape and values
                   (result.1.size = m) ∧
                   (∀ i : Fin m, result.1.get i = Vector.replicate 1 (seq1.get i)) ∧
                   -- Second array has correct shape and values  
                   (result.2.size = 1) ∧
                   (∀ j : Fin 1, result.2.get j = seq2) ∧
                   -- Mesh property: coordinates are preserved
                   (∀ i : Fin m, ∀ j : Fin n, 
                     (result.1.get i).get ⟨0, zero_lt_one⟩ = seq1.get i ∧
                     (result.2.get ⟨0, zero_lt_one⟩).get j = seq2.get j)⌝⦄ := by
  simp [ix_]
  constructor
  · simp [Vector.map_size]
  constructor
  · intro i
    simp [Vector.get_map]
  constructor
  · simp [Vector.replicate_size]
  constructor
  · intro j
    simp [Vector.get_replicate]
  · intro i j
    constructor
    · simp [Vector.get_map, Vector.get_replicate]
    · simp [Vector.get_replicate]