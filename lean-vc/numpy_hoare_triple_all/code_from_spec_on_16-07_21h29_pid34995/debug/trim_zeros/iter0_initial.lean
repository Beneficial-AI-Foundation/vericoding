import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.trim_zeros",
  "category": "Adding Removing Elements",
  "description": "Trim the leading and/or trailing zeros from a 1-D array or sequence",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.trim_zeros.html",
  "doc": "Trim the leading and/or trailing zeros from a 1-D array or sequence.\n\nParameters\n----------\nfilt : 1-D array or sequence\n    Input array.\ntrim : str, optional\n    A string with 'f' representing trim from front and 'b' to trim from\n    back. Default is 'fb', trim zeros from both front and back of the\n    array.\n\nReturns\n-------\ntrimmed : 1-D array or sequence\n    The result of trimming the input. The input data type is preserved.\n\nExamples\n--------\n>>> a = np.array((0, 0, 0, 1, 2, 3, 0, 2, 1, 0))\n>>> np.trim_zeros(a)\narray([1, 2, 3, 0, 2, 1])\n>>> np.trim_zeros(a, 'b')\narray([0, 0, 0, 1, 2, 3, 0, 2, 1])\n\nThe input data type is preserved, list/tuple in means list/tuple out.\n\n>>> np.trim_zeros([0, 1, 2, 0])\n[1, 2]",
  "code": "# Implementation in numpy/lib/_function_base_impl.py\n# See NumPy source code repository",
  "source_location": "numpy/lib/_function_base_impl.py",
  "signature": "numpy.trim_zeros(filt, trim='fb')"
}
-/

open Std.Do

/-- Represents the trim mode for trim_zeros function -/
inductive TrimMode where
  /-- Trim zeros from the front of the array only (corresponds to 'f') -/
  | Front
  /-- Trim zeros from the back of the array only (corresponds to 'b') -/
  | Back
  /-- Trim zeros from both front and back of the array (corresponds to 'fb', default) -/
  | Both

-- LLM HELPER
/-- Find the first non-zero element index from the front -/
def find_first_nonzero {n : Nat} (arr : Vector Float n) : Nat :=
  let rec go (i : Nat) : Nat :=
    if h : i < n then
      if arr.get ⟨i, h⟩ = 0 then
        go (i + 1)
      else
        i
    else
      n
  go 0

-- LLM HELPER
/-- Find the last non-zero element index from the back -/
def find_last_nonzero {n : Nat} (arr : Vector Float n) : Nat :=
  let rec go (i : Nat) : Nat :=
    if i = 0 then
      0
    else
      let idx := i - 1
      if h : idx < n then
        if arr.get ⟨idx, h⟩ = 0 then
          go idx
        else
          i
      else
        0
  go n

-- LLM HELPER
/-- Extract subvector from start to end -/
def extract_subvector {n : Nat} (arr : Vector Float n) (start : Nat) (finish : Nat) :
    Vector Float (if start ≤ finish ∧ finish ≤ n then finish - start else 0) :=
  if h : start ≤ finish ∧ finish ≤ n then
    Vector.ofFn (fun i => arr.get ⟨start + i, by
      have : i.val < finish - start := i.isLt
      have : start + i.val < finish := by
        rw [Nat.add_comm]
        exact Nat.add_lt_of_lt_sub this
      exact Nat.lt_of_lt_of_le this h.2
    ⟩)
  else
    Vector.ofFn (fun i => 0)

/-- numpy.trim_zeros: Trim the leading and/or trailing zeros from a 1-D array.
    
    Removes zeros from the beginning and/or end of a vector based on the trim mode.
    - Front: removes leading zeros only
    - Back: removes trailing zeros only
    - Both: removes both leading and trailing zeros (default)
    
    The function preserves all non-zero elements and internal zeros.
-/
def trim_zeros {n : Nat} (arr : Vector Float n) (mode : TrimMode := TrimMode.Both) : 
    Id (Σ m : Nat, Vector Float m) :=
  let start := match mode with
    | TrimMode.Front => find_first_nonzero arr
    | TrimMode.Back => 0
    | TrimMode.Both => find_first_nonzero arr
  
  let finish := match mode with
    | TrimMode.Front => n
    | TrimMode.Back => find_last_nonzero arr
    | TrimMode.Both => find_last_nonzero arr
  
  let result_size := if start ≤ finish then finish - start else 0
  let result_vec := extract_subvector arr start finish
  
  if h : start ≤ finish ∧ finish ≤ n then
    ⟨result_size, result_vec⟩
  else
    ⟨0, Vector.ofFn (fun _ => 0)⟩

/-- Specification: trim_zeros removes leading and/or trailing zeros while preserving order.
    
    The function guarantees:
    1. All non-zero elements from the original array are preserved in order
    2. Internal zeros (zeros between non-zero elements) are preserved
    3. Only leading/trailing zeros are removed based on the mode
    4. If the array contains only zeros, returns an empty vector
-/
theorem trim_zeros_spec {n : Nat} (arr : Vector Float n) (mode : TrimMode) :
    ⦃⌜True⌝⦄
    trim_zeros arr mode
    ⦃⇓result => ⌜
      -- Define the range of preserved elements
      ∃ (start finish : Nat) (h_start : start ≤ n) (h_finish : finish ≤ n) (h_order : start ≤ finish),
        -- The trimmed size matches the preserved range
        result.1 = finish - start ∧
        -- Elements before start are zeros (if trimming front)
        (mode = TrimMode.Front ∨ mode = TrimMode.Both → 
          ∀ i : Fin start, arr.get ⟨i, Nat.lt_of_lt_of_le i.isLt h_start⟩ = 0) ∧
        -- Elements after finish are zeros (if trimming back)
        (mode = TrimMode.Back ∨ mode = TrimMode.Both → 
          ∀ i : Fin (n - finish), arr.get ⟨finish + i, Nat.add_lt_of_lt_sub i.isLt (Nat.sub_le n finish)⟩ = 0) ∧
        -- The preserved elements match exactly
        (∀ i : Fin result.1, result.2.get i = arr.get ⟨start + i, Nat.add_lt_of_lt_sub i.isLt (Eq.symm (Nat.add_sub_cancel start finish) ▸ Nat.add_le_of_le_sub h_order h_finish)⟩) ∧
        -- If trimming front, start is the first non-zero or n
        (mode = TrimMode.Front ∨ mode = TrimMode.Both → 
          (start = n ∨ arr.get ⟨start, Nat.lt_of_lt_of_le (Nat.lt_of_le_of_ne (Nat.zero_le start) (Ne.symm (Nat.ne_of_lt (Nat.pos_of_ne_zero (fun h => by cases h))))) h_start⟩ ≠ 0)) ∧
        -- If trimming back, finish is past the last non-zero or 0
        (mode = TrimMode.Back ∨ mode = TrimMode.Both → 
          (finish = 0 ∨ arr.get ⟨finish - 1, Nat.sub_lt (Nat.pos_of_ne_zero (fun h => by cases h)) (Nat.le_refl 1)⟩ ≠ 0))
    ⌝⦄ := by
  simp [trim_zeros]
  use 0, n, Nat.zero_le n, Nat.le_refl n, Nat.zero_le n
  simp
  sorry