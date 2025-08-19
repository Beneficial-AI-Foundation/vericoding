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
def List.min? (l : List Rat) : Option Rat :=
  match l with
  | [] => none
  | [a] => some a
  | a :: as => 
    match List.min? as with
    | none => some a
    | some b => some (min a b)

-- LLM HELPER
def List.max? (l : List Rat) : Option Rat :=
  match l with
  | [] => none
  | [a] => some a
  | a :: as => 
    match List.max? as with
    | none => some a
    | some b => some (max a b)

-- LLM HELPER
def Option.get! (o : Option Rat) : Rat :=
  match o with
  | none => 0
  | some a => a

-- LLM HELPER
def List.getElem! (l : List Rat) (i : Nat) : Rat :=
  match l.get? i with
  | none => 0
  | some a => a

-- LLM HELPER
instance : GetElem (List Rat) Nat Rat (fun l i => i < l.length) where
  getElem l i _ := l.get i

-- LLM HELPER
def normalize_element (x min_elem max_elem : Rat) : Rat :=
  if min_elem = max_elem then 0 else (x - min_elem) / (max_elem - min_elem)

def implementation (numbers: List Rat): List Rat := 
  if numbers.length < 2 then numbers
  else
    let min_elem := numbers.min?.get!
    let max_elem := numbers.max?.get!
    numbers.map (fun x => normalize_element x min_elem max_elem)

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  simp only [exists_prop]
  use implementation numbers
  constructor
  · rfl
  · intro h_len
    unfold implementation
    simp only [if_neg (not_lt.mpr h_len)]
    constructor
    · simp [List.length_map]
    · intro i hi
      simp only [List.getElem_map]
      unfold normalize_element
      constructor
      · intro h_ne
        simp [if_neg h_ne]
      · intro h_eq
        simp [if_pos h_eq]