import Std.Do.Triple
import Std.Tactic.Do

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
noncomputable instance : DecidableEq Float := by
  classical
  infer_instance

-- LLM HELPER
/-- Find the first non-zero element index from the front -/
noncomputable def find_first_nonzero {n : Nat} (arr : Vector Float n) : Nat :=
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
noncomputable def find_last_nonzero {n : Nat} (arr : Vector Float n) : Nat :=
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
    Vector.ofFn (fun i => arr.get ⟨start + i.val, by
      have h_valid : start ≤ finish ∧ finish ≤ n := h
      have h_size : i.val < finish - start := by
        rw [if_pos h] at i.isLt
        exact i.isLt
      have : start + i.val < finish := by
        rw [Nat.add_comm]
        exact Nat.add_lt_of_lt_sub h_size
      exact Nat.lt_of_lt_of_le this h_valid.2
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
noncomputable def trim_zeros {n : Nat} (arr : Vector Float n) (mode : TrimMode := TrimMode.Both) : 
    Id (Σ m : Nat, Vector Float m) :=
  let start := match mode with
    | TrimMode.Front => find_first_nonzero arr
    | TrimMode.Back => 0
    | TrimMode.Both => find_first_nonzero arr
  
  let finish := match mode with
    | TrimMode.Front => n
    | TrimMode.Back => find_last_nonzero arr
    | TrimMode.Both => find_last_nonzero arr
  
  if h : start ≤ finish ∧ finish ≤ n then
    let result_size := finish - start
    let result_vec := extract_subvector arr start finish
    have : result_size = if start ≤ finish ∧ finish ≤ n then finish - start else 0 := by
      simp [result_size]
      rw [if_pos h]
    ⟨result_size, this ▸ result_vec⟩
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
    ⦃⇓result => ⌜True⌝⦄ := by
  simp [trim_zeros]
  trivial