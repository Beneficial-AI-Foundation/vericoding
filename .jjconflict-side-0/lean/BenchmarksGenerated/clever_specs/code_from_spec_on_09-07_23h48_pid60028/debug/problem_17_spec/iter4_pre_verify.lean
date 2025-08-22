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

def implementation (string: String) : List Nat := 
  let not_map := fun
    | "o" => 4
    | "o|" => 2
    | ".|" => 1
    | _ => 0
  let space_split := string.splitOn " "
  space_split.map not_map

-- LLM HELPER
lemma list_map_length {α β : Type*} (f : α → β) (l : List α) : 
  (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [List.map, ih]

-- LLM HELPER
lemma list_map_get {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
  (l.map f)[i]! = f (l[i]!) := by
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
: problem_spec implementation string := by
  let not_map := fun
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
      rw [list_map_get not_map space_split i]
      simp [list_map_length] at hi
      exact hi