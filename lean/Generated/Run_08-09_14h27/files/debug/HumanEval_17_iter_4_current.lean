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
  rw [List.getElem!_map, List.getElem!_pos _ h]

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
    · simp [List.length_map]
    · intro i hi
      rw [list_map_get]
      simp only
      rfl