import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) : List Nat :=
  let tokens := string.splitOn " "
  tokens.map (fun token => 
    match token with
    | "o" => 4
    | "o|" => 2
    | ".|" => 1
    | _ => 0)

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
∀ i < result.length, not_map (space_split[i]!) = result[i]!;
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
lemma list_map_length {α β : Type*} (f : α → β) (l : List α) : 
  (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [List.map, ih]

-- LLM HELPER  
lemma list_map_get {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < (l.map f).length) :
  (l.map f)[i]! = f (l[i]!) := by
  rw [list_map_length] at h
  induction l generalizing i with
  | nil => simp at h
  | cons head tail ih =>
    cases i with
    | zero => simp [List.map]
    | succ j => 
      simp [List.map]
      apply ih
      simp at h
      exact Nat.lt_of_succ_lt_succ h

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  unfold problem_spec implementation
  let tokens := string.splitOn " "
  let result := tokens.map (fun token => 
    match token with
    | "o" => 4
    | "o|" => 2
    | ".|" => 1
    | _ => 0)
  use result
  constructor
  · rfl
  · constructor
    · exact list_map_length _ _
    · intro i hi
      rw [list_map_get]
      simp only [implementation]
      rfl