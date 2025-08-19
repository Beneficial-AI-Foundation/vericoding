import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.roll",
  "category": "Rearranging Elements",
  "description": "Roll array elements along a given axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.roll.html",
  "doc": "Roll array elements along a given axis.\n\nElements that roll beyond the last position are re-introduced at\nthe first.\n\nParameters\n----------\na : array_like\n    Input array.\nshift : int or tuple of ints\n    The number of places by which elements are shifted. If a tuple,\n    then \`axis\` must be a tuple of the same size, and each of the\n    given axes is shifted by the corresponding number. If an int\n    while \`axis\` is a tuple of ints, then the same value is used for\n    all given axes.\naxis : int or tuple of ints, optional\n    Axis or axes along which elements are shifted. By default, the\n    array is flattened before shifting, after which the original\n    shape is restored.\n\nReturns\n-------\nres : ndarray\n    Output array, with the same shape as \`a\`.\n\nExamples\n--------\n>>> x = np.arange(10)\n>>> np.roll(x, 2)\narray([8, 9, 0, 1, 2, 3, 4, 5, 6, 7])\n>>> np.roll(x, -2)\narray([2, 3, 4, 5, 6, 7, 8, 9, 0, 1])\n\n>>> x2 = np.reshape(x, (2, 5))\n>>> x2\narray([[0, 1, 2, 3, 4],\n       [5, 6, 7, 8, 9]])\n>>> np.roll(x2, 1)\narray([[9, 0, 1, 2, 3],\n       [4, 5, 6, 7, 8]])\n>>> np.roll(x2, -1)\narray([[1, 2, 3, 4, 5],\n       [6, 7, 8, 9, 0]])\n>>> np.roll(x2, 1, axis=0)\narray([[5, 6, 7, 8, 9],\n       [0, 1, 2, 3, 4]])\n>>> np.roll(x2, -1, axis=0)\narray([[5, 6, 7, 8, 9],\n       [0, 1, 2, 3, 4]])\n>>> np.roll(x2, 1, axis=1)\narray([[4, 0, 1, 2, 3],\n       [9, 5, 6, 7, 8]])\n>>> np.roll(x2, -1, axis=1)\narray([[1, 2, 3, 4, 0],\n       [6, 7, 8, 9, 5]])\n>>> np.roll(x2, (1, 1), axis=(1, 0))\narray([[9, 5, 6, 7, 8],\n       [4, 0, 1, 2, 3]])\n>>> np.roll(x2, (2, 1), axis=(1, 0))\narray([[8, 9, 5, 6, 7],\n       [3, 4, 0, 1, 2]])",
  "code": "# Implementation in numpy/_core/numeric.py\n# See NumPy source code repository",
  "source_location": "numpy/_core/numeric.py",
  "signature": "numpy.roll(a, shift, axis=None)"
}
-/

open Std.Do

-- LLM HELPER
def normalizeIndex (i : Int) (n : Nat) : Nat :=
  if n = 0 then 0 else ((i % n) + n) % n |>.toNat

-- LLM HELPER
lemma normalizeIndex_lt (i : Int) (n : Nat) (h : n > 0) : 
  normalizeIndex i n < n := by
  simp [normalizeIndex]
  split
  · contradiction
  · have : ((i % n) + n) % n < n := by
      apply Int.mod_lt_of_pos
      simp [Int.add_pos_iff]
      exact Int.pos_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (ne_of_gt h))
    exact Int.natAbs_of_nonneg (Int.mod_nonneg _ (Int.ne_of_gt (Int.pos_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (ne_of_gt h)))))

/-- Roll array elements along a given axis by cyclically shifting elements.
    Elements that roll beyond the last position are re-introduced at the first. -/
def roll {n : Nat} {α : Type} (a : Vector α n) (shift : Int) : Id (Vector α n) :=
  if n = 0 then pure a else
  pure ⟨fun i => 
    let srcIdx := normalizeIndex (i.val - shift) n
    a.get ⟨srcIdx, normalizeIndex_lt (i.val - shift) n (Nat.pos_of_ne_zero (ne_of_gt (Nat.pos_of_ne_zero (Fin.size_pos' i))))⟩⟩

-- LLM HELPER
lemma normalizeIndex_spec (i : Int) (n : Nat) (h : n > 0) :
  let result := normalizeIndex i n
  let srcIdx := i % (n : Int)
  let normalizedIdx := if srcIdx < 0 then srcIdx + n else srcIdx
  result = normalizedIdx.toNat := by
  simp [normalizeIndex]
  rw [if_neg (ne_of_gt h)]
  simp [Int.add_mod]
  by_cases h' : i % n < 0
  · simp [if_pos h']
    rw [Int.mod_add_mod]
    have : (i % n + n) % n = i % n + n := by
      rw [Int.add_mod]
      simp
      rw [Int.mod_self, Int.add_zero]
      rw [Int.mod_mod_of_dvd]
      exact dvd_refl _
    rw [this]
    rw [Int.toNat_of_nonneg]
    exact Int.add_nonneg (Int.le_of_lt h') (Int.pos_iff_ne_zero.mp (Nat.cast_pos.mpr h))
  · simp [if_neg h']
    have : i % n ≥ 0 := Int.not_lt.mp h'
    rw [Int.add_mod]
    simp
    rw [Int.mod_self, Int.add_zero]
    rw [Int.mod_mod_of_dvd]
    · rw [Int.toNat_of_nonneg this]
    · exact dvd_refl _

/-- Specification: roll cyclically shifts array elements by the given amount.
    For positive shift, elements move to the right and wrap around.
    For negative shift, elements move to the left and wrap around.
    Empty vectors are returned unchanged.
    
    Mathematical property: result[i] = a[(i - shift) mod n]
    where the modulo operation handles negative values correctly. -/
theorem roll_spec {n : Nat} {α : Type} (a : Vector α n) (shift : Int) :
    ⦃⌜True⌝⦄
    roll a shift
    ⦃⇓result => ⌜(n = 0 → result = a) ∧ 
                 (n > 0 → ∀ i : Fin n, 
                   let srcIdx := ((i.val : Int) - shift) % (n : Int)
                   let normalizedIdx := if srcIdx < 0 then srcIdx + n else srcIdx
                   result.get i = a.get ⟨normalizedIdx.toNat, by sorry⟩)⌝⦄ := by
  simp [roll]
  split
  · simp
    intro h
    rfl
  · next h =>
    simp
    intro h_pos i
    have h_ne : n ≠ 0 := ne_of_gt h_pos
    simp [Vector.get]
    have : normalizeIndex (i.val - shift) n = 
           (if ((i.val : Int) - shift) % (n : Int) < 0 
            then ((i.val : Int) - shift) % (n : Int) + n 
            else ((i.val : Int) - shift) % (n : Int)).toNat := by
      exact normalizeIndex_spec (i.val - shift) n h_pos
    rw [this]
    congr 1
    congr 1
    rfl