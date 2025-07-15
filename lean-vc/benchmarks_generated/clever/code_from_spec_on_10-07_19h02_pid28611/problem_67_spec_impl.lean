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

-- LLM HELPER
lemma string_join_eq_concat (x y : Nat) :
  String.join [x.repr, " apples and ", y.repr, " oranges"] = 
  x.repr ++ " apples and " ++ y.repr ++ " oranges" := by
  simp [String.join]

def implementation (string: String) (n: Nat) : Nat :=
  match parse_apples_oranges string with
  | some (x, y) => if x + y ≤ n then n - (x + y) else n
  | none => n

theorem correctness
(s: String) (n : Nat)
: problem_spec implementation s n := by
  unfold problem_spec
  unfold implementation
  cases h : parse_apples_oranges s with
  | none => 
    use n
    constructor
    · rfl
    · use 0, 0
      constructor
      · simp
      · rw [string_join_eq_concat]
        simp [String.join, Nat.repr]
  | some val =>
    match val with
    | (x, y) =>
      by_cases hle : x + y ≤ n
      · use n - (x + y)
        constructor
        · simp [hle]
        · use x, y
          constructor
          · simp
          · rw [string_join_eq_concat]
            simp [String.join]
      · use n
        constructor
        · simp [hle]
        · use 0, 0
          constructor
          · simp
          · rw [string_join_eq_concat]
            simp [String.join, Nat.repr]