def problem_spec
-- function signature
(implementation: List Rat → List Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: List Rat) :=
2 ≤ numbers.length →
let min_elem := numbers.minimum?.get!;
let max_elem := numbers.maximum?.get!;
let range := max_elem - min_elem;
result.length = numbers.length ∧
∀ i, i < numbers.length →
(min_elem ≠ max_elem →
result[i]! = (numbers[i]! - min_elem) / range) ∧
(min_elem = max_elem →
result[i]! = 0);
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def normalize_element (val min_elem max_elem : Rat) : Rat :=
if min_elem = max_elem then 0 else (val - min_elem) / (max_elem - min_elem)

def implementation (numbers: List Rat): List Rat := 
if numbers.length < 2 then numbers
else
  let min_elem := numbers.minimum?.get!
  let max_elem := numbers.maximum?.get!
  numbers.map (fun x => normalize_element x min_elem max_elem)

-- LLM HELPER
lemma length_map_eq {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [List.length_cons, List.map_cons, ih]

-- LLM HELPER
lemma get_map {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
  (l.map f)[i]! = f (l[i]!) := by
  induction l generalizing i with
  | nil => simp at h
  | cons head tail ih =>
    cases i with
    | zero => simp [List.getElem!_cons_zero]
    | succ j => 
      simp [List.getElem!_cons_succ]
      apply ih
      simp at h
      exact Nat.lt_of_succ_lt_succ h

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · intro h_len
    unfold implementation
    simp [if_neg (not_lt.mpr h_len)]
    constructor
    · exact length_map_eq _ _
    · intro i hi
      rw [get_map]
      unfold normalize_element
      constructor
      · intro h_ne
        simp [if_neg h_ne]
      · intro h_eq
        simp [if_pos h_eq]