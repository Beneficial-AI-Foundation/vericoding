import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def get_even_indices (l: List Int) : List Nat :=
  (List.range l.length).filter (λ i => i % 2 = 0)

-- LLM HELPER  
def get_even_values (l: List Int) : List Int :=
  let even_idx := get_even_indices l
  even_idx.map (λ i => l[i]!)

-- LLM HELPER
def set_at_indices (l: List Int) (indices: List Nat) (values: List Int) : List Int :=
  match indices, values with
  | [], _ => l
  | _, [] => l
  | i::is, v::vs => 
    let updated := l.set i v
    set_at_indices updated is vs

-- LLM HELPER
def int_le_dec (a b : Int) : Bool := a ≤ b

def implementation (l: List Int) : List Int :=
  let even_idx := get_even_indices l
  let even_val := get_even_values l
  let sorted_even := even_val.mergeSort int_le_dec
  set_at_indices l even_idx sorted_even

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: List Int) :=
  l.length = result.length ∧
  let even_idx := (List.range l.length).filter (λ i => i % 2 = 0);
  let even_val_in_result := even_idx.map (λ i => result[i]!);
  let even_val := even_idx.map (λ i => l[i]!);
  (∀ i, i < l.length → (i % 2 ≠ 0 → l[i]! = result[i]!)) ∧
  List.Sorted Int.le even_val_in_result ∧
  even_val.all (λ x => even_val_in_result.count x = even_val.count x);
-- program termination
∃ result, implementation l = result ∧
spec result

-- LLM HELPER
lemma set_at_indices_length (l: List Int) (indices: List Nat) (values: List Int) :
  (set_at_indices l indices values).length = l.length := by
  induction indices generalizing l values with
  | nil => simp [set_at_indices]
  | cons i is ih =>
    cases values with
    | nil => simp [set_at_indices]
    | cons v vs => 
      simp [set_at_indices]
      rw [ih]
      simp [List.length_set]

-- LLM HELPER
lemma set_at_indices_preserves_odd (l: List Int) (indices: List Nat) (values: List Int) 
  (h_even: ∀ i ∈ indices, i % 2 = 0) :
  ∀ i, i < l.length → (i % 2 ≠ 0 → l[i]! = (set_at_indices l indices values)[i]!) := by
  intro i hi hodd
  induction indices generalizing l values with
  | nil => simp [set_at_indices]
  | cons idx idxs ih =>
    cases values with
    | nil => simp [set_at_indices]
    | cons v vs =>
      simp [set_at_indices]
      have h_even_idx : idx % 2 = 0 := h_even idx (by simp)
      have h_even_rest : ∀ i ∈ idxs, i % 2 = 0 := λ i hi => h_even i (by simp [hi])
      by_cases h : i = idx
      · rw [h] at hodd
        rw [h_even_idx] at hodd
        simp at hodd
      · rw [List.getElem_set_ne]
        apply ih h_even_rest
        rw [List.length_set] at hi
        exact hi
        exact h

-- LLM HELPER
lemma mergeSort_sorted (l: List Int) : List.Sorted Int.le (l.mergeSort int_le_dec) := by
  apply List.sorted_mergeSort

-- LLM HELPER  
lemma mergeSort_count (l: List Int) (x: Int) : (l.mergeSort int_le_dec).count x = l.count x := by
  apply List.count_mergeSort

theorem correctness
(l: List Int)
: problem_spec implementation l
:= by
  simp [problem_spec]
  use implementation l
  constructor
  · rfl
  · simp [implementation]
    constructor
    · rw [set_at_indices_length]
    · constructor
      · simp [get_even_indices]
        apply set_at_indices_preserves_odd
        intro i hi
        simp [List.mem_filter, List.mem_range] at hi
        exact hi.2
      · constructor
        · simp [get_even_indices, get_even_values]
          apply mergeSort_sorted
        · simp [get_even_indices, get_even_values, List.all_eq_true]
          intro x
          rw [mergeSort_count]