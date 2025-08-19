import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Rat → List Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: List Rat) :=
2 ≤ numbers.length →
let min_elem := numbers.min?.get!;
let max_elem := numbers.max?.get!;
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
def normalize_single (x min_elem max_elem : Rat) : Rat :=
  if min_elem = max_elem then 0 else (x - min_elem) / (max_elem - min_elem)

def implementation (numbers: List Rat): List Rat := 
  if numbers.length < 2 then numbers
  else
    let min_elem := numbers.min?.get!
    let max_elem := numbers.max?.get!
    numbers.map (fun x => normalize_single x min_elem max_elem)

-- LLM HELPER
lemma list_getelem_map {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
  (l.map f)[i]! = f (l[i]!) := by
  rw [List.getElem!_eq_getElem_get_or_else]
  rw [List.getElem_map]
  rw [List.getElem!_eq_getElem_get_or_else]

-- LLM HELPER
lemma list_length_map {α β : Type*} (f : α → β) (l : List α) : 
  (l.map f).length = l.length := List.length_map

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  simp only [implementation]
  split_ifs with h
  · -- Case: numbers.length < 2
    use numbers
    constructor
    · rfl
    · intro h_len
      exfalso
      omega
  · -- Case: numbers.length ≥ 2
    use numbers.map (fun x => normalize_single x numbers.min?.get! numbers.max?.get!)
    constructor
    · rfl
    · intro h_len
      constructor
      · rw [list_length_map]
      · intro i hi
        rw [list_getelem_map]
        unfold normalize_single
        constructor
        · intro h_ne
          simp [h_ne]
        · intro h_eq
          simp [h_eq]