import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List Int → Int)
-- inputs
(arr: List Int) :=
-- spec
let spec (result: Int) :=
  ¬arr.any (fun x => 1 < arr.count x) →
  (arr.length = 0 ∨ arr.length = 1 → result = -1) ∧
  (1 < arr.length →
    let last := arr.length-1;
    let i := if arr[last]! < arr[last-1]! then Int.ofNat last else -1;
    result = max (impl (arr.take last)) i);
-- program termination
∃ result, impl arr = result ∧
-- return value satisfies spec
spec result

def implementation (arr: List Int) : Int := 
  if arr.length ≤ 1 then 
    -1
  else
    let last := arr.length - 1
    let i := if arr[last]! < arr[last - 1]! then Int.ofNat last else -1
    max (implementation (arr.take last)) i

-- LLM HELPER
lemma take_length_lt (arr : List Int) (h : 1 < arr.length) : (arr.take (arr.length - 1)).length < arr.length := by
  rw [List.length_take]
  simp only [min_def]
  split_ifs with h1
  · exact Nat.sub_lt (Nat.pos_of_ne_zero (ne_of_gt (Nat.zero_lt_of_ne_zero (ne_of_gt h)))) (by norm_num)
  · exact h

-- LLM HELPER
lemma take_preserves_no_duplicates (arr : List Int) : 
  ¬arr.any (fun x => 1 < arr.count x) → 
  ¬(arr.take (arr.length - 1)).any (fun x => 1 < (arr.take (arr.length - 1)).count x) := by
  intro h
  intro h_contra
  apply h
  rw [List.any_iff_exists] at h_contra ⊢
  obtain ⟨x, hx_mem, hx_count⟩ := h_contra
  use x
  constructor
  · rw [List.mem_take] at hx_mem
    exact hx_mem.1
  · rw [List.mem_take] at hx_mem
    have h_count_le : (arr.take (arr.length - 1)).count x ≤ arr.count x := by
      apply List.count_take_le
    linarith

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  unfold problem_spec
  have h_term : ∃ result, implementation arr = result := ⟨implementation arr, rfl⟩
  use implementation arr
  constructor
  · rfl
  · intro h_no_dup
    constructor
    · intro h_short
      unfold implementation
      split_ifs with h_len
      · rfl
      · exfalso
        cases h_short with
        | inl h_zero => 
          have : arr.length > 0 := Nat.not_le.mp h_len
          linarith
        | inr h_one =>
          have : arr.length > 1 := Nat.not_le.mp h_len
          linarith
    · intro h_long
      unfold implementation
      split_ifs with h_len
      · exfalso
        linarith
      · simp only [not_le] at h_len
        rfl

termination_by arr.length
decreasing_by 
  simp_wf
  apply take_length_lt
  simp only [not_le] at h_len
  exact h_len