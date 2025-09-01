/- 
{
  "name": "numpy.array_split",
  "category": "Splitting Arrays",
  "description": "Split an array into multiple sub-arrays",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.array_split.html",
  "doc": "Split an array into multiple sub-arrays.\n\nPlease refer to the \`split\` documentation. The only difference\nbetween these functions is that \`array_split\` allows\n\`indices_or_sections\` to be an integer that does *not* equally\ndivide the axis. For an array of length l that should be split\ninto n sections, it returns l % n sub-arrays of size l//n + 1\nand the rest of size l//n.\n\nExamples\n--------\n>>> x = np.arange(8.0)\n>>> np.array_split(x, 3)\n[array([0.,  1.,  2.]), array([3.,  4.,  5.]), array([6.,  7.])]",
  "source_location": "numpy/lib/_shape_base_impl.py",
  "signature": "numpy.array_split(ary, indices_or_sections, axis=0)"
}
-/

/-  Split a vector into k sub-vectors.
    
    When splitting a vector of length n into k sections:
    - The first (n % k) sub-vectors have size ⌈n/k⌉ = (n + k - 1) / k
    - The remaining sub-vectors have size ⌊n/k⌋ = n / k
    
    This ensures all elements are distributed as evenly as possible,
    with larger sub-vectors appearing first.
-/

/-  Specification: array_split distributes elements evenly with mathematical properties
    
    The specification captures:
    1. Size distribution: larger chunks come first
    2. Element preservation: all elements from the original vector appear in order
    3. No gaps or overlaps: elements are contiguously distributed
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def array_split {n k : Nat} (v : Vector Float n) (hk : k > 0) : 
    Id (Vector (Σ m : Nat, Vector Float m) k) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem array_split_spec {n k : Nat} (v : Vector Float n) (hk : k > 0) :
    ⦃⌜k > 0⌝⦄
    array_split v hk
    ⦃⇓result => ⌜
      -- Each sub-vector has the correct size based on its position
      (∀ i : Fin k, 
        (result.get i).1 = 
          if i.val < n % k then (n + k - 1) / k else n / k) ∧
      -- Elements are preserved in order across all sub-vectors
      (∃ (start_indices : Vector Nat k),
        -- First sub-vector starts at index 0
        start_indices.get ⟨0, by omega⟩ = 0 ∧
        -- Each subsequent sub-vector starts where the previous one ended
        (∀ i : Fin k, i.val > 0 → 
          start_indices.get i = start_indices.get ⟨i.val - 1, by omega⟩ + 
            (result.get ⟨i.val - 1, by omega⟩).1) ∧
        -- Elements match the original vector
        (∀ i : Fin k, ∀ j : Fin (result.get i).1,
          (result.get i).2.get j = 
            v.get ⟨start_indices.get i + j.val, by sorry⟩))
    ⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
