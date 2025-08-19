import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.ascontiguousarray",
  "category": "From existing data",
  "description": "Return a contiguous array (ndim >= 1) in memory (C order)",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ascontiguousarray.html",
  "doc": "\nReturn a contiguous array (ndim >= 1) in memory (C order).\n\nParameters\n----------\na : array_like\n    Input array.\ndtype : str or dtype object, optional\n    Data-type of returned array.\nlike : array_like, optional\n    Reference object to allow the creation of arrays which are not NumPy arrays.\n\nReturns\n-------\nout : ndarray\n    Contiguous array of same shape and content as a, with type dtype if specified.\n\nExamples\n--------\n>>> x = np.arange(6).reshape(2,3)\n>>> np.ascontiguousarray(x, dtype=np.float32)\narray([[0., 1., 2.],\n       [3., 4., 5.]], dtype=float32)\n>>> x.flags['C_CONTIGUOUS']\nTrue\n\nNote: This function returns at least a 1-dimensional array. Scalar inputs are converted to 1-dimensional arrays.\n",
  "code": "@array_function_dispatch(_ascontiguousarray_dispatcher)\ndef ascontiguousarray(a, dtype=None, *, like=None):\n    \"\"\"\n    Return a contiguous array (ndim >= 1) in memory (C order).\n    \"\"\"\n    if like is not None:\n        return _ascontiguousarray_with_like(a, dtype=dtype, like=like)\n\n    return array(a, dtype, copy=False, order='C', ndmin=1)",
  "signature": "numpy.ascontiguousarray(a, dtype=None, *, like=None)"
}
-/

-- LLM HELPER
lemma max_n_1_pos (n : Nat) : max n 1 ≥ 1 := by
  simp [Nat.max_def]
  split
  · assumption
  · simp

-- LLM HELPER  
lemma max_n_1_eq_n {n : Nat} (h : n > 0) : max n 1 = n := by
  simp [Nat.max_def]
  split
  · rfl
  · omega

-- LLM HELPER
lemma max_0_1_eq_1 : max 0 1 = 1 := by
  simp [Nat.max_def]

-- LLM HELPER
def vector_with_default {α : Type*} (v : Vector α n) (default : α) : Vector α (max n 1) :=
  if h : n = 0 then
    have : max n 1 = 1 := by rw [h]; exact max_0_1_eq_1
    this ▸ Vector.cons default Vector.nil
  else
    have : max n 1 = n := by
      apply max_n_1_eq_n
      omega
    this ▸ v

def problem_spec {n : Nat} (impl : Vector Float n → Id (Vector Float (max n 1))) (a : Vector Float n) : Prop :=
  ⦃⌜True⌝⦄
  impl a
  ⦃⇓result => ⌜
    (max n 1 ≥ 1) ∧
    (n > 0 → max n 1 = n) ∧
    (n = 0 → max n 1 = 1) ∧
    (n > 0 → ∀ i : Fin n, ∃ j : Fin (max n 1), result.get j = a.get i)
  ⌝⦄

def implementation {n : Nat} (a : Vector Float n) : Id (Vector Float (max n 1)) :=
  pure (vector_with_default a 0.0)

theorem correctness {n : Nat} (a : Vector Float n) : problem_spec implementation a := by
  simp [problem_spec, implementation]
  apply ⟨⟩
  · exact max_n_1_pos n
  · intro h
    exact max_n_1_eq_n h
  · intro h
    rw [h]
    exact max_0_1_eq_1
  · intro h_pos i
    simp [vector_with_default]
    split
    · rename_i h_eq
      exfalso
      rw [h_eq] at h_pos
      omega
    · rename_i h_ne
      have : max n 1 = n := max_n_1_eq_n h_pos
      exists this ▸ i
      simp