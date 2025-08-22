import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → List Nat)
-- inputs
(string: String) :=
-- spec
let not_map := fun
  | "o" => 4
  | "o|" => 2
  | ".|" => 1
  | _ => 0;
let spec (result: List Nat) :=
let space_split := string.splitOn " ";
space_split.length = result.length ∧
∀ i < result.length, not_map (space_split.get! i) = result.get! i;
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
def not_map : String → Nat := fun
  | "o" => 4
  | "o|" => 2
  | ".|" => 1
  | _ => 0

def implementation (string: String) : List Nat := 
  (string.splitOn " ").map not_map

-- LLM HELPER
lemma list_map_length (f : String → Nat) (l : List String) : 
  (l.map f).length = l.length := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [List.map, List.length, ih]

-- LLM HELPER
lemma list_map_get (f : String → Nat) (l : List String) (i : Nat) (h : i < l.length) :
  (l.map f).get! i = f (l.get! i) := by
  induction l generalizing i with
  | nil => simp at h
  | cons head tail ih =>
    cases i with
    | zero => simp [List.get!, List.map]
    | succ j => 
      simp [List.get!, List.map]
      apply ih
      simp at h
      exact Nat.lt_of_succ_lt_succ h

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  simp [problem_spec, implementation]
  let not_map_local := fun
    | "o" => 4
    | "o|" => 2
    | ".|" => 1
    | _ => 0
  let space_split := string.splitOn " "
  let result := space_split.map not_map
  use result
  constructor
  · rfl
  · constructor
    · exact list_map_length not_map space_split
    · intro i hi
      rw [list_map_get]
      rfl