-- LLM HELPER
def digits (base : Nat) : Nat → List Nat
  | 0 => [0]
  | n + 1 => 
    let rec aux (n : Nat) (acc : List Nat) : List Nat :=
      if n = 0 then acc
      else aux (n / base) ((n % base) :: acc)
    termination_by n
    aux (n + 1) []

-- LLM HELPER
inductive Sorted (r : α → α → Prop) : List α → Prop where
  | nil : Sorted r []
  | single (a : α) : Sorted r [a]
  | cons {a b : α} {l : List α} : r a b → Sorted r (b :: l) → Sorted r (a :: b :: l)

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(x: List Nat) :=
-- spec
let spec (result: List Nat) :=
  let has_even_digits(i: Nat): Bool :=
    decide ((List.filter (fun d => decide (d % 2 = 0)) (digits 10 i)).length > 0);
  (Sorted Nat.le result) ∧
  (forall i, i ∈ result ↔ (i ∈ x ∧ !(has_even_digits i) = true))
-- program termination
∃ result, implementation x = result ∧
spec result

-- LLM HELPER
def has_even_digits (i: Nat): Bool :=
  decide ((List.filter (fun d => decide (d % 2 = 0)) (digits 10 i)).length > 0)

-- LLM HELPER
def filter_no_even_digits (x: List Nat) : List Nat :=
  List.filter (fun i => !(has_even_digits i)) x

-- LLM HELPER
lemma filter_mem_iff (p : Nat → Bool) (l : List Nat) (a : Nat) :
  a ∈ List.filter p l ↔ a ∈ l ∧ p a = true := by
  exact List.mem_filter

-- LLM HELPER
lemma sorted_sort (l : List Nat) : Sorted Nat.le (List.mergeSort l) := by
  induction l using List.strong_induction_on with
  | h l ih =>
    cases l with
    | nil => exact Sorted.nil
    | cons a l' => 
      cases l' with
      | nil => exact Sorted.single a
      | cons b l'' =>
        have h1 : List.mergeSort l = List.mergeSort (a :: b :: l'') := rfl
        rw [h1]
        have : List.mergeSort (a :: b :: l'') = List.mergeSort [a, b] := by
          simp [List.mergeSort]
        have : Sorted Nat.le (List.mergeSort [a, b]) := by
          simp [List.mergeSort]
          if h : a ≤ b then
            simp [h]
            exact Sorted.cons h (Sorted.single b)
          else
            simp [h]
            have : b ≤ a := Nat.le_of_not_gt (fun h' => h (Nat.le_of_lt h'))
            exact Sorted.cons this (Sorted.single a)
        exact this

-- LLM HELPER
lemma mem_sort_iff (l : List Nat) (a : Nat) : a ∈ List.mergeSort l ↔ a ∈ l := by
  exact List.mem_mergeSort

def implementation (x: List Nat) : List Nat := 
  List.mergeSort (filter_no_even_digits x)

theorem correctness
(x: List Nat)
: problem_spec implementation x := by
  unfold problem_spec
  use List.mergeSort (filter_no_even_digits x)
  constructor
  · rfl
  · constructor
    · apply sorted_sort
    · intro i
      constructor
      · intro h
        rw [mem_sort_iff] at h
        unfold filter_no_even_digits at h
        rw [filter_mem_iff] at h
        constructor
        · exact h.1
        · exact h.2
      · intro h
        rw [mem_sort_iff]
        unfold filter_no_even_digits
        rw [filter_mem_iff]
        constructor
        · exact h.1
        · exact h.2