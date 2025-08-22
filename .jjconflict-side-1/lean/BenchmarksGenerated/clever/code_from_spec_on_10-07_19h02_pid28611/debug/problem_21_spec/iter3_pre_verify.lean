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
def normalize_helper (numbers: List Rat) (min_elem max_elem: Rat) : List Rat :=
  if min_elem = max_elem then
    List.replicate numbers.length 0
  else
    let range := max_elem - min_elem
    numbers.map (fun x => (x - min_elem) / range)

def implementation (numbers: List Rat): List Rat := 
  if numbers.length < 2 then
    numbers
  else
    let min_elem := numbers.min?.get!
    let max_elem := numbers.max?.get!
    normalize_helper numbers min_elem max_elem

-- LLM HELPER
lemma list_length_replicate (n : Nat) (x : Rat) : (List.replicate n x).length = n := by
  simp [List.length_replicate]

-- LLM HELPER
lemma list_length_map {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  simp [List.length_map]

-- LLM HELPER
lemma list_get_replicate (n : Nat) (x : Rat) (i : Nat) (hi : i < n) : 
  (List.replicate n x)[i]?.getD default = x := by
  simp [List.getElem?_replicate, hi]

-- LLM HELPER
lemma list_get_map {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (i : Nat) (hi : i < l.length) :
  (l.map f)[i]?.getD default = f (l[i]?.getD default) := by
  simp [List.getElem?_map, hi]

-- LLM HELPER
lemma normalize_helper_length (numbers: List Rat) (min_elem max_elem: Rat) :
  (normalize_helper numbers min_elem max_elem).length = numbers.length := by
  unfold normalize_helper
  split_ifs
  · exact list_length_replicate numbers.length 0
  · exact list_length_map _ numbers

-- LLM HELPER
lemma normalize_helper_get_eq_case (numbers: List Rat) (min_elem max_elem: Rat) 
  (h_eq : min_elem = max_elem) (i : Nat) (hi : i < numbers.length) :
  (normalize_helper numbers min_elem max_elem)[i]?.getD default = 0 := by
  unfold normalize_helper
  simp [h_eq]
  exact list_get_replicate numbers.length 0 i hi

-- LLM HELPER
lemma normalize_helper_get_ne_case (numbers: List Rat) (min_elem max_elem: Rat) 
  (h_ne : min_elem ≠ max_elem) (i : Nat) (hi : i < numbers.length) :
  (normalize_helper numbers min_elem max_elem)[i]?.getD default = (numbers[i]?.getD default - min_elem) / (max_elem - min_elem) := by
  unfold normalize_helper
  simp [h_ne]
  rw [list_get_map]
  exact hi

-- LLM HELPER
lemma getElem_eq_get {α : Type*} [Inhabited α] (l : List α) (i : Nat) (hi : i < l.length) :
  l[i]! = l[i]?.getD default := by
  simp [List.getElem_eq_get]

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec
  simp
  use implementation numbers
  constructor
  · rfl
  · intro h_len
    unfold implementation
    simp [h_len]
    let min_elem := numbers.min?.get!
    let max_elem := numbers.max?.get!
    constructor
    · exact normalize_helper_length numbers min_elem max_elem
    · intro i hi
      constructor
      · intro h_ne
        rw [← getElem_eq_get, ← getElem_eq_get]
        exact normalize_helper_get_ne_case numbers min_elem max_elem h_ne i hi
      · intro h_eq
        rw [← getElem_eq_get]
        exact normalize_helper_get_eq_case numbers min_elem max_elem h_eq i hi