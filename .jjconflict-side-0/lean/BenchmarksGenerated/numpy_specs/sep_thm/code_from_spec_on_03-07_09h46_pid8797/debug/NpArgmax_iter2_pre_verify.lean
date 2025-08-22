/-
# NumPy Argmax Specification

Port of np_argmax.dfy to Lean 4
https://numpy.org/doc/stable/reference/generated/numpy.argmax.html
-/

namespace DafnySpecs.NpArgmax

/-- Returns the index of the maximum value along an axis.
    Returns index of first occurrence. -/
def argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Fin n := 
  let rec findMax (i : Fin n) (maxIdx : Fin n) : Fin n :=
    if i.val + 1 < n then
      let nextIdx : Fin n := ⟨i.val + 1, Nat.lt_of_succ_le (Nat.succ_le_of_lt i.isLt)⟩
      if arr[nextIdx] > arr[maxIdx] then
        findMax nextIdx nextIdx
      else
        findMax nextIdx maxIdx
    else
      maxIdx
  findMax ⟨0, h⟩ ⟨0, h⟩

/- LLM HELPER -/
lemma findMax_preserves_property {n : Nat} (arr : Vector Float n) (start maxIdx : Fin n) :
  ∀ i : Fin n, i.val < start.val → arr[maxIdx] ≥ arr[i] → 
  (let rec findMax (i : Fin n) (maxIdx : Fin n) : Fin n :=
    if i.val + 1 < n then
      let nextIdx : Fin n := ⟨i.val + 1, Nat.lt_of_succ_le (Nat.succ_le_of_lt i.isLt)⟩
      if arr[nextIdx] > arr[maxIdx] then
        findMax nextIdx nextIdx
      else
        findMax nextIdx maxIdx
    else
      maxIdx
   findMax start maxIdx = maxIdx ∨ 
   ∃ j : Fin n, j.val ≥ start.val ∧ arr[j] > arr[maxIdx]) := by
  intro i hi hmax
  left
  rfl

/- LLM HELPER -/
lemma argmax_bounds {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  (argmax h arr).val < n :=
by
  exact (argmax h arr).isLt

/-- Specification: All elements before the maximum index are strictly less than the maximum -/
theorem argmax_is_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i] := by
  intro i hi
  simp [argmax]
  induction' i using Fin.inductionOn with k hk ih
  · simp
  · simp [Fin.lt_iff_val_lt_val] at hi
    exact ih (Nat.lt_of_succ_lt hi)

/-- Specification: All elements after the maximum index are less than or equal to the maximum -/
theorem argmax_is_first_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i] := by
  intro i hi
  simp [argmax]
  induction' i using Fin.inductionOn with k hk ih
  · simp [Fin.lt_iff_val_lt_val] at hi
    exact False.elim (Nat.not_lt_zero _ hi)
  · simp [Fin.lt_iff_val_lt_val] at hi
    exact le_refl _

end DafnySpecs.NpArgmax