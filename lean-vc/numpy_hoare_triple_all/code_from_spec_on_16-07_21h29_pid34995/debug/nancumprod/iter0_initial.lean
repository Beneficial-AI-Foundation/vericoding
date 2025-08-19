import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.nancumprod",
  "description": "Return the cumulative product of array elements over a given axis treating Not a Numbers (NaNs) as one",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.nancumprod.html",
  "doc": "Return the cumulative product of array elements over a given axis treating Not a Numbers (NaNs) as one.",
  "code": "Implemented in numpy/lib/nanfunctions.py"
}
-/

open Std.Do

-- LLM HELPER
def nancumprod_helper {n : Nat} (arr : Vector Float n) (i : Nat) (acc : Float) : Float :=
  if h : i < n then
    let val := arr.get ⟨i, h⟩
    let new_acc := if Float.isNaN val then acc else acc * val
    nancumprod_helper arr (i + 1) new_acc
  else acc

/-- Return the cumulative product of array elements treating NaNs as 1.
    The cumulative product does not change when NaNs are encountered and leading NaNs are replaced by ones. -/
def nancumprod {n : Nat} (arr : Vector Float n) : Id (Vector Float n) :=
  Id.pure (Vector.ofFn (fun i => 
    (List.range (i.val + 1)).foldl (fun acc idx => 
      let val := arr.get ⟨idx, by 
        have : idx < i.val + 1 := List.mem_range.mp (by simp [List.mem_range])
        have : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
        exact Nat.lt_of_lt_of_le this this⟩
      if Float.isNaN val then acc else acc * val) 1.0))

-- LLM HELPER
lemma list_range_bound (i : Nat) (idx : Nat) (h : idx ∈ List.range (i + 1)) : idx ≤ i :=
  List.mem_range.mp h

-- LLM HELPER
lemma fin_bound_helper {n : Nat} (i : Fin n) (idx : Nat) (h : idx ∈ List.range (i.val + 1)) : idx < n :=
  have h1 : idx < i.val + 1 := List.mem_range.mp h
  have h2 : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
  Nat.lt_of_lt_of_le h1 h2

/-- Specification: nancumprod returns the cumulative product while treating NaN values as 1.
    This means:
    1. The resulting array has the same size as the input
    2. Each element is the product of all non-NaN elements from the start up to that position
    3. NaN values are treated as 1 in the product calculation
    4. Leading NaNs are replaced by ones
    5. The cumulative product property holds for non-NaN values -/
theorem nancumprod_spec {n : Nat} (arr : Vector Float n) :
    ⦃⌜True⌝⦄
    nancumprod arr
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- If all elements from start to i are NaN, result[i] = 1
      (∀ j : Fin n, j.val ≤ i.val → Float.isNaN (arr.get j)) → result.get i = 1.0 ∧
      -- If no elements from start to i are NaN, result[i] = product of all elements from start to i
      (∀ j : Fin n, j.val ≤ i.val → ¬Float.isNaN (arr.get j)) → 
        result.get i = (List.range (i.val + 1)).foldl (fun acc idx => acc * arr.get ⟨idx, by exact fin_bound_helper i idx (by assumption)⟩) 1.0 ∧
      -- General case: result[i] = product of all non-NaN elements from start to i
      result.get i = (List.range (i.val + 1)).foldl (fun acc idx => 
        let val := arr.get ⟨idx, by exact fin_bound_helper i idx (by assumption)⟩
        if Float.isNaN val then acc else acc * val) 1.0⌝⦄ := by
  apply triple_intro
  · simp
  · intro result h_result
    simp [nancumprod] at h_result
    rw [← h_result]
    intro i
    constructor
    · intro h_all_nan
      simp [Vector.get, Vector.ofFn]
      have : (List.range (i.val + 1)).foldl (fun acc idx => 
        let val := arr.get ⟨idx, fin_bound_helper i idx (List.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_refl idx)))⟩
        if Float.isNaN val then acc else acc * val) 1.0 = 1.0 := by
          apply List.foldl_ext
          intro acc idx h_mem
          have : idx ≤ i.val := list_range_bound (i.val) idx h_mem
          have : Float.isNaN (arr.get ⟨idx, fin_bound_helper i idx h_mem⟩) := 
            h_all_nan ⟨idx, fin_bound_helper i idx h_mem⟩ this
          simp [this]
      exact this
    constructor
    · intro h_no_nan
      simp [Vector.get, Vector.ofFn]
      apply List.foldl_ext
      intro acc idx h_mem
      have : ¬Float.isNaN (arr.get ⟨idx, fin_bound_helper i idx h_mem⟩) := 
        h_no_nan ⟨idx, fin_bound_helper i idx h_mem⟩ (list_range_bound (i.val) idx h_mem)
      simp [this]
    · simp [Vector.get, Vector.ofFn]
      rfl