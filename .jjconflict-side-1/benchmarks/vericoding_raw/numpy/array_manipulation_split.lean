import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.split",
  "category": "Splitting Arrays",
  "description": "Split an array into multiple sub-arrays",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.split.html",
  "doc": "Split an array into multiple sub-arrays as views into \`ary\`.\n\nParameters\n----------\nary : ndarray\n    Array to be divided into sub-arrays.\nindices_or_sections : int or 1-D array\n    If \`indices_or_sections\` is an integer, N, the array will be divided\n    into N equal arrays along \`axis\`. If such a split is not possible,\n    an error is raised.\n    \n    If \`indices_or_sections\` is a 1-D array of sorted integers, the entries\n    indicate where along \`axis\` the array is split. For example,\n    \`\`[2, 3]\`\` would, for \`\`axis=0\`\`, result in\n    \n    - ary[:2]\n    - ary[2:3]\n    - ary[3:]\n    \n    If an index exceeds the dimension of the array along \`axis\`,\n    an empty sub-array is returned correspondingly.\naxis : int, optional\n    The axis along which to split, default is 0.\n\nReturns\n-------\nsub-arrays : list of ndarrays\n    A list of sub-arrays as views into \`ary\`.\n\nExamples\n--------\n>>> x = np.arange(9.0)\n>>> np.split(x, 3)\n[array([0.,  1.,  2.]), array([3.,  4.,  5.]), array([6.,  7.,  8.])]\n>>> x = np.arange(8.0)\n>>> np.split(x, [3, 5, 6, 10])\n[array([0.,  1.,  2.]),\n array([3.,  4.]),\n array([5.]),\n array([6.,  7.]),\n array([], dtype=float64)]",
  "code": "# Implementation in numpy/lib/_shape_base_impl.py\n# See NumPy source code repository",
  "source_location": "numpy/lib/_shape_base_impl.py",
  "signature": "numpy.split(ary, indices_or_sections, axis=0)"
}
-/

open Std.Do

/-- Split a vector into k equal parts. Requires that the vector length is divisible by k -/
def split {n k : Nat} (arr : Vector Float n) (h_div : k ∣ n) (h_pos : k > 0) : 
    Id (Vector (Vector Float (n / k)) k) :=
  sorry

/-- Specification: split divides a vector into k equal-sized sub-vectors 
    where each sub-vector contains consecutive elements from the original.
    
    The specification states that:
    1. The result is a vector of k sub-vectors
    2. Each sub-vector has size n/k 
    3. Element j of sub-vector i corresponds to element (i * (n/k) + j) of the original vector
    4. All elements from the original vector are preserved in the split
-/
theorem split_spec {n k : Nat} (arr : Vector Float n) (h_div : k ∣ n) (h_pos : k > 0) :
    ⦃⌜k ∣ n ∧ k > 0⌝⦄
    split arr h_div h_pos
    ⦃⇓result => ⌜(∀ i : Fin k, ∀ j : Fin (n / k), 
                  ∃ (idx : Fin n), idx.val = i.val * (n / k) + j.val ∧ 
                  (result.get i).get j = arr.get idx) ∧
                 (∀ idx : Fin n, ∃ (i : Fin k) (j : Fin (n / k)), 
                  idx.val = i.val * (n / k) + j.val ∧
                  arr.get idx = (result.get i).get j)⌝⦄ := by
  sorry