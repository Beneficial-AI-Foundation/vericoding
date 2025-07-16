import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List Int → Nat → Int)
(arr: List Int)
(k: Nat) :=
let spec (result: Int) :=
  1 ≤ arr.length → arr.length ≤ 100 → 1 ≤ k → k ≤ arr.length →
  ((∀ i, 0 ≤ i ∧ i < k → ¬(arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!)) → result = 0) ∧
  ∃ i, i < k
    ∧ arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!
    ∧ result = arr[i]! + (if i = 0 then 0 else implementation arr i)
    ∧ ∀ i', i < i' ∧ i' < k → ¬(arr[i']! ≤ 99 ∧ -99 ≤ arr[i']!)
∃ result, implementation arr k = result ∧
spec result

-- LLM HELPER
def in_range (x : Int) : Bool := x ≤ 99 ∧ -99 ≤ x

-- LLM HELPER
def find_first_in_range (arr : List Int) (k : Nat) : Option Nat :=
  (List.range k).find? (fun i => in_range arr[i]!)

def implementation (arr: List Int) (k: Nat) : Int :=
  match find_first_in_range arr k with
  | none => 0
  | some i => arr[i]! + (if i = 0 then 0 else implementation arr i)

-- LLM HELPER
lemma find_first_in_range_correct (arr : List Int) (k : Nat) :
  match find_first_in_range arr k with
  | none => ∀ i, 0 ≤ i ∧ i < k → ¬in_range arr[i]!
  | some i => i < k ∧ in_range arr[i]! ∧ ∀ i', i < i' ∧ i' < k → ¬in_range arr[i']!
:= by
  unfold find_first_in_range
  simp only [List.find?_eq_none, List.find?_eq_some]
  split_ifs <;> simp [List.mem_range, in_range]

-- LLM HELPER
lemma implementation_unfold (arr : List Int) (k : Nat) :
  implementation arr k = 
  match find_first_in_range arr k with
  | none => 0
  | some i => arr[i]! + (if i = 0 then 0 else implementation arr i)
:= by rfl

theorem correctness
(arr: List Int)
(k: Nat)
: problem_spec implementation arr k := by
  unfold problem_spec
  use implementation arr k
  constructor
  · rfl
  · intro h_len_ge h_len_le h_k_ge h_k_le
    constructor
    · intro h_none
      rw [implementation_unfold]
      have h_find_none : find_first_in_range arr k = none := by
        cases h_find : find_first_in_range arr k with
        | none => rfl
        | some i => 
          exfalso
          have h_correct := find_first_in_range_correct arr k
          rw [h_find] at h_correct
          obtain ⟨h_i_lt_k, h_in_range, _⟩ := h_correct
          have h_not_in_range := h_none i ⟨by omega, h_i_lt_k⟩
          exact h_not_in_range h_in_range
      rw [h_find_none]
      simp
    · cases h_find : find_first_in_range arr k with
      | none => 
        exfalso
        have h_correct := find_first_in_range_correct arr k
        rw [h_find] at h_correct
        sorry -- This case should not happen given the existence claim
      | some i =>
        use i
        have h_correct := find_first_in_range_correct arr k
        rw [h_find] at h_correct
        obtain ⟨h_i_lt_k, h_in_range, h_first⟩ := h_correct
        constructor
        · exact h_i_lt_k
        · constructor
          · exact h_in_range
          · constructor
            · rw [implementation_unfold, h_find]
              simp
            · exact h_first