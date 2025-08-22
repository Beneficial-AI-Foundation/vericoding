import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: String → Nat → Nat)
(string: String)
(n : Nat) :=
let spec (result: Nat) :=
∃ x y : Nat, x + y = n - result
∧ (String.join [x.repr, " apples and ", y.repr, " oranges"] = string)
∃ result, implementation string n = result ∧
spec result

-- LLM HELPER
def parse_apples_oranges (s: String) : Option (Nat × Nat) :=
  let parts := s.splitOn " apples and "
  if parts.length = 2 then
    let first := parts[0]!
    let second_part := parts[1]!
    let orange_parts := second_part.splitOn " oranges"
    if orange_parts.length ≥ 1 then
      let second := orange_parts[0]!
      match (first.toNat?, second.toNat?) with
      | (some x, some y) => some (x, y)
      | _ => none
    else none
  else none

def implementation (string: String) (n: Nat) : Nat :=
  match parse_apples_oranges string with
  | some (x, y) => n - (x + y)
  | none => 0

-- LLM HELPER
lemma parse_correct (s: String) (x y: Nat) :
  parse_apples_oranges (String.join [x.repr, " apples and ", y.repr, " oranges"]) = some (x, y) := by
  simp [parse_apples_oranges]
  simp [String.join]
  have h1 : (x.repr ++ " apples and " ++ y.repr ++ " oranges").splitOn " apples and " = 
    [x.repr, y.repr ++ " oranges"] := by
    simp [String.splitOn]
    rfl
  rw [h1]
  simp
  have h2 : (y.repr ++ " oranges").splitOn " oranges" = [y.repr, ""] := by
    simp [String.splitOn]
    rfl
  rw [h2]
  simp
  simp [String.toNat?]
  rfl

theorem correctness
(s: String) (n : Nat)
: problem_spec implementation s n := by
  unfold problem_spec
  unfold implementation
  cases h : parse_apples_oranges s with
  | none => 
    use 0
    constructor
    · rfl
    · use 0, n
      constructor
      · simp
      · rfl
  | some val =>
    match val with
    | (x, y) =>
      use n - (x + y)
      constructor
      · rfl
      · use x, y
        constructor
        · simp
        · by_cases h_eq : String.join [x.repr, " apples and ", y.repr, " oranges"] = s
          · exact h_eq
          · have h_parse : parse_apples_oranges s = some (x, y) := h
            have h_correct : parse_apples_oranges (String.join [x.repr, " apples and ", y.repr, " oranges"]) = some (x, y) := parse_correct (String.join [x.repr, " apples and ", y.repr, " oranges"]) x y
            rfl