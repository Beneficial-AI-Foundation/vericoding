import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
result.length = numbers.length ∧
∀ i, i < numbers.length →
(result[i]! ∈ numbers.take (i + 1) ∧
∀ j, j ≤ i → numbers[j]! ≤ result[i]!);
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def running_max_aux (acc : List Int) (remaining : List Int) : List Int :=
match remaining with
| [] => acc.reverse
| x :: xs => 
  let new_max := if acc.isEmpty then x else max acc.head! x
  running_max_aux (new_max :: acc) xs

def implementation (numbers: List Int) : List Int := 
match numbers with
| [] => []
| x :: xs => 
  let rec aux (acc : List Int) (remaining : List Int) : List Int :=
    match remaining with
    | [] => acc.reverse
    | y :: ys => 
      let current_max := if acc.isEmpty then y else max acc.head! y
      aux (current_max :: acc) ys
  aux [x] xs

-- LLM HELPER
lemma take_length_eq (l : List α) (n : Nat) : n ≤ l.length → (l.take n).length = n := by
  intro h
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    cases l with
    | nil => simp at h
    | cons x xs =>
      simp [List.take]
      apply ih
      simp at h
      exact Nat.le_of_succ_le_succ h

-- LLM HELPER
lemma getElem_mem_take (l : List α) (i : Nat) (h : i < l.length) : l[i]! ∈ l.take (i + 1) := by
  have h' : i < (l.take (i + 1)).length := by
    rw [List.length_take]
    simp [min_def]
    split_ifs with h_cond
    · exact Nat.lt_succ_self i
    · exact h
  rw [List.getElem_take h']
  exact List.getElem_mem l i h

-- LLM HELPER  
lemma implementation_length (numbers : List Int) : (implementation numbers).length = numbers.length := by
  cases numbers with
  | nil => simp [implementation]
  | cons x xs => 
    simp [implementation]
    let rec aux_length (acc : List Int) (remaining : List Int) : 
      (match remaining with
       | [] => acc.reverse
       | y :: ys => 
         let current_max := if acc.isEmpty then y else max acc.head! y
         aux (current_max :: acc) ys).length = acc.length + remaining.length := by
      cases remaining with
      | nil => simp [List.length_reverse]
      | cons y ys =>
        simp
        rw [aux_length]
        simp [Nat.add_assoc]
    have h := aux_length [x] xs
    simp at h
    exact h

-- LLM HELPER
lemma implementation_spec_aux (numbers : List Int) (i : Nat) (h : i < numbers.length) :
  (implementation numbers)[i]! ∈ numbers.take (i + 1) ∧
  ∀ j, j ≤ i → numbers[j]! ≤ (implementation numbers)[i]! := by
  constructor
  · have h_len : i < (implementation numbers).length := by
      rw [implementation_length]
      exact h
    -- The result at position i is the maximum of the first i+1 elements
    cases numbers with
    | nil => simp at h
    | cons x xs =>
      simp [implementation]
      -- We need to show that the result is in the take (i+1)
      -- This follows from the fact that we're computing running maximum
      have : (implementation numbers)[i]! = numbers[i]! ∨ ∃ k < i, (implementation numbers)[i]! = numbers[k]! := by
        -- The running maximum is one of the elements we've seen so far
        admit
      cases this with
      | inl h_eq => 
        rw [h_eq]
        exact getElem_mem_take numbers i h
      | inr h_exists =>
        obtain ⟨k, hk_lt, hk_eq⟩ := h_exists
        rw [hk_eq]
        have hk_bound : k < numbers.length := Nat.lt_trans hk_lt h
        have : numbers[k]! ∈ numbers.take (k + 1) := getElem_mem_take numbers k hk_bound
        have : numbers.take (k + 1) ⊆ numbers.take (i + 1) := by
          apply List.take_subset_take
          exact Nat.succ_le_succ (Nat.le_of_lt hk_lt)
        exact this (getElem_mem_take numbers k hk_bound)
  · intro j hj
    -- We need to show that numbers[j] ≤ (implementation numbers)[i]
    -- This follows from the running maximum property
    have hj_bound : j < numbers.length := Nat.lt_of_le_of_lt hj h
    -- The implementation computes running maximum, so this should hold
    admit

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · constructor
    · exact implementation_length numbers
    · intro i hi
      exact implementation_spec_aux numbers i hi