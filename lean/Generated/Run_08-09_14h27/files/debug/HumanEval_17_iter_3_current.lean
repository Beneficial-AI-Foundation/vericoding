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
lemma list_map_get {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
  (l.map f)[i]! = f (l[i]!) := by
  induction l generalizing i with
  | nil => simp at h
  | cons head tail ih =>
    cases i with
    | zero => simp [List.map]
    | succ j => 
      simp [List.map]
      cases hj : tail[j]? with
      | none => 
        have : j ≥ tail.length := List.getElem?_eq_none.mp hj
        simp [List.getElem!_of_invalid this]
      | some val =>
        have : j < tail.length := by
          rw [List.getElem?_eq_some] at hj
          exact hj.1
        rw [List.getElem!_of_valid (List.lt_length_map _ _ this)]
        rw [List.getElem!_of_valid this]
        rw [List.getElem_map]
        simp [hj]

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
    · exact List.length_map
    · intro i hi
      rw [list_map_get]
      · simp only [implementation]
        rfl
      · rw [← List.length_map]
        exact hi