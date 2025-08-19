import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "ufunc.accumulate",
  "category": "Accumulation Method",
  "description": "Accumulate the result of applying operator to all elements",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ufunc.accumulate.html",
  "signature": "ufunc.accumulate(array, axis=0, dtype=None, out=None)",
  "parameters": {
    "array": "Input array",
    "axis": "Axis along which to accumulate",
    "dtype": "Data type for intermediate results",
    "out": "Location for the result"
  },
  "example": "np.add.accumulate([2, 3, 5])  # Returns [2, 5, 10]\nnp.multiply.accumulate([2, 3, 5])  # Returns [2, 6, 30]",
  "notes": [
    "Returns array of same shape with intermediate results",
    "For add.accumulate, equivalent to cumsum()",
    "For multiply.accumulate, equivalent to cumprod()"
  ]
}
-/

/-- 
Universal function accumulate method: Accumulate the result of applying a binary operator
to all elements in a vector.

For a binary operation `op` and input vector [a₁, a₂, a₃, ..., aₙ], returns:
[a₁, op(a₁, a₂), op(op(a₁, a₂), a₃), ..., op(op(...op(a₁, a₂), a₃), ..., aₙ)]

This generalizes cumulative operations:
- When op = (+), this becomes cumsum: [a₁, a₁+a₂, a₁+a₂+a₃, ...]
- When op = (*), this becomes cumprod: [a₁, a₁*a₂, a₁*a₂*a₃, ...]

The result has the same shape as the input array.
-/
def accumulate {n : Nat} (op : Float → Float → Float) (a : Vector Float n) : Id (Vector Float n) :=
  if h : n = 0 then
    Vector.cast h a
  else
    let first := a.get ⟨0, Nat.pos_of_ne_zero h⟩
    let result := Array.mkEmpty n
    let result := result.push first
    let finalResult := (List.range (n - 1)).foldl
      (fun acc i => 
        let prevIdx := i
        let currIdx := i + 1
        let prev := acc.get! prevIdx
        let curr := a.get ⟨currIdx, Nat.add_lt_of_lt_sub (List.mem_range.mp (List.mem_of_mem_filter (fun x => x < n - 1) ⟨i, rfl⟩)) h⟩
        acc.push (op prev curr))
      result
    Vector.mk finalResult

-- LLM HELPER
lemma vector_length_pos {n : Nat} (a : Vector Float n) (h : n ≠ 0) : 0 < n :=
  Nat.pos_of_ne_zero h

-- LLM HELPER
lemma succ_lt_of_lt_pred {i n : Nat} (h : i < n - 1) (hn : n ≠ 0) : i + 1 < n := by
  cases' n with n
  · contradiction
  · simp at h
    exact Nat.add_lt_succ_of_le (Nat.le_of_lt_succ h)

/-- 
Specification: accumulate applies a binary operator cumulatively to produce
intermediate results at each position.

Precondition: True (works for any vector and binary operation)
Postcondition:
- Result has same length as input
- First element equals first element of input (when n > 0)
- Each subsequent element is the result of applying the operator to the previous 
  accumulated result and the current element
- Mathematically: result[i] = op(op(...op(a[0], a[1]), a[2]), ..., a[i])

Mathematical Properties:
- result[0] = a[0] (when n > 0)
- result[i] = op(result[i-1], a[i]) for i > 0 (recurrence relation)
- Each element represents the accumulated result of the operation from start to that position
- The operation is applied left-associatively: ((a[0] op a[1]) op a[2]) op ... op a[i]
-/
theorem accumulate_spec {n : Nat} (op : Float → Float → Float) (a : Vector Float n) :
    ⦃⌜True⌝⦄
    accumulate op a
    ⦃⇓result => ⌜
      -- Result has same length as input
      result.toList.length = n ∧
      -- For non-empty vectors, first element equals first element of input
      (n > 0 → result.get ⟨0, by simp [Nat.pos_iff_ne_zero]; intro h; rw [h]; simp⟩ = a.get ⟨0, by simp [Nat.pos_iff_ne_zero]; intro h; rw [h]; simp⟩) ∧
      -- Recurrence relation: each element is op applied to previous result and current element
      (∀ i : Fin n, i.val > 0 → 
        result.get i = op (result.get ⟨i.val - 1, by simp; exact Nat.sub_lt (Nat.pos_of_ne_zero (ne_of_gt i.isLt)) (by simp)⟩) (a.get i)) ∧
      -- Cumulative accumulation property: each element is the left-associative fold of all previous elements
      (n > 0 → ∀ i : Fin n, result.get i = (a.toList.take (i.val + 1)).tail.foldl op (a.get ⟨0, by simp [Nat.pos_iff_ne_zero]; intro h; rw [h]; simp⟩))
    ⌝⦄ := by
  intro h
  simp [accumulate]
  split
  · next h_eq =>
    simp [h_eq]
    constructor
    · simp [Vector.toList_length]
    constructor
    · intro h_pos
      rw [h_eq] at h_pos
      simp at h_pos
    constructor
    · intro i h_gt
      rw [h_eq] at i
      simp at i
    · intro h_pos
      rw [h_eq] at h_pos
      simp at h_pos
  · next h_ne =>
    constructor
    · simp [Vector.toList_length]
    constructor
    · intro h_pos
      simp
    constructor
    · intro i h_gt
      simp
    · intro h_pos i
      simp