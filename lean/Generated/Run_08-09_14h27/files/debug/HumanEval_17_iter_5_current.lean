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
  have h_map : i < (l.map f).length := by simp [List.length_map, h]
  rw [List.getElem!_pos _ h_map, List.getElem!_pos _ h]
  rw [List.getElem_map]

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
    · exact List.length_map _ _
    · intro i hi
      have h_len : i < tokens.length := by simp [List.length_map] at hi; exact hi
      rw [list_map_get _ _ _ h_len]
      rfl