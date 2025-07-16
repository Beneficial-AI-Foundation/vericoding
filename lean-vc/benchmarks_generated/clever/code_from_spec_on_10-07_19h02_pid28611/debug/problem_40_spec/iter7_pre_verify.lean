import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List Int → Bool)
(numbers: List Int) :=
let sum_i_j_k (i j k: Nat) : Bool :=
  numbers[i]! + numbers[j]! + numbers[k]! = 0;
let exists_zero := 3 ≤ numbers.length ∧ (∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
 i < numbers.length ∧ j < numbers.length ∧ k < numbers.length ∧
 sum_i_j_k i j k)
let spec (result: Bool) :=
result ↔ exists_zero
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def check_three_sum_aux (numbers: List Int) (i j k: Nat) : Bool :=
  if i < numbers.length ∧ j < numbers.length ∧ k < numbers.length then
    numbers[i]?.getD 0 + numbers[j]?.getD 0 + numbers[k]?.getD 0 = 0
  else
    false

-- LLM HELPER
def check_all_triplets (numbers: List Int) : Bool :=
  if numbers.length < 3 then false
  else
    let n := numbers.length
    (List.range n).any fun i =>
      (List.range n).any fun j =>
        (List.range n).any fun k =>
          i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ check_three_sum_aux numbers i j k

def implementation (numbers: List Int) : Bool := check_all_triplets numbers

-- LLM HELPER
lemma check_three_sum_aux_correct (numbers: List Int) (i j k: Nat) :
  check_three_sum_aux numbers i j k = true ↔ 
  (i < numbers.length ∧ j < numbers.length ∧ k < numbers.length ∧ 
   numbers[i]?.getD 0 + numbers[j]?.getD 0 + numbers[k]?.getD 0 = 0) := by
  simp [check_three_sum_aux]
  constructor
  · intro h
    exact h
  · intro h
    simp [h]

-- LLM HELPER
lemma List.any_eq_true_iff {α : Type*} (l : List α) (p : α → Bool) :
  l.any p = true ↔ ∃ a ∈ l, p a = true := by
  simp [List.any_eq_true]

-- LLM HELPER
lemma List.mem_range_iff (n : Nat) (i : Nat) : i ∈ List.range n ↔ i < n := by
  simp [List.mem_range]

-- LLM HELPER
lemma getD_eq_get_of_mem (l : List Int) (i : Nat) (hi : i < l.length) (default : Int) :
  l[i]?.getD default = l[i]! := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers := by
  simp [problem_spec, implementation]
  use check_all_triplets numbers
  constructor
  · rfl
  · simp [check_all_triplets]
    constructor
    · intro h
      cases' h with hlen h
      · simp at hlen
        linarith
      · simp [List.any_eq_true_iff, List.mem_range_iff] at h
        obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk, hsum⟩ := h
        simp [check_three_sum_aux_correct] at hsum
        obtain ⟨hi_lt, hj_lt, hk_lt, hsum_eq⟩ := hsum
        constructor
        · linarith
        · use i, j, k
          constructor
          · exact hij
          · constructor
            · exact hik
            · constructor
              · exact hjk
              · constructor
                · exact hi_lt
                · constructor
                  · exact hj_lt
                  · constructor
                    · exact hk_lt
                    · simp only [problem_spec]
                      rw [← getD_eq_get_of_mem numbers i hi_lt 0,
                          ← getD_eq_get_of_mem numbers j hj_lt 0,
                          ← getD_eq_get_of_mem numbers k hk_lt 0]
                      exact hsum_eq
    · intro h
      obtain ⟨hlen, i, j, k, hij, hik, hjk, hi, hj, hk, hsum⟩ := h
      right
      simp [List.any_eq_true_iff, List.mem_range_iff]
      use i, hi, j, hj, k, hk
      constructor
      · exact hij
      · constructor
        · exact hik
        · constructor
          · exact hjk
          · simp [check_three_sum_aux_correct, hi, hj, hk]
            rw [getD_eq_get_of_mem numbers i hi 0,
                getD_eq_get_of_mem numbers j hj 0,
                getD_eq_get_of_mem numbers k hk 0]
            exact hsum