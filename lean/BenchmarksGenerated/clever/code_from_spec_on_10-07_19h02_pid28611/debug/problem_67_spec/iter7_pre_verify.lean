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
  | some (x, y) => if x + y ≤ n then n - (x + y) else 0
  | none => 0

-- LLM HELPER
lemma string_join_eq_concat (x y : Nat) :
  String.join [x.repr, " apples and ", y.repr, " oranges"] = 
  x.repr ++ " apples and " ++ y.repr ++ " oranges" := by
  simp [String.join]

-- LLM HELPER
lemma parse_splits_correctly (x y : Nat) :
  let s := x.repr ++ " apples and " ++ y.repr ++ " oranges"
  let parts := s.splitOn " apples and "
  parts.length = 2 ∧
  parts[0]! = x.repr ∧
  parts[1]! = y.repr ++ " oranges" := by
  simp [String.splitOn]
  constructor
  · rfl
  · constructor
    · rfl
    · rfl

-- LLM HELPER
lemma parse_oranges_correctly (y : Nat) :
  let orange_parts := (y.repr ++ " oranges").splitOn " oranges"
  orange_parts.length ≥ 1 ∧
  orange_parts[0]! = y.repr := by
  simp [String.splitOn]
  constructor
  · rfl
  · rfl

-- LLM HELPER
lemma string_join_parse (x y : Nat) :
  parse_apples_oranges (x.repr ++ " apples and " ++ y.repr ++ " oranges") = some (x, y) := by
  unfold parse_apples_oranges
  have h1 := parse_splits_correctly x y
  have h2 := parse_oranges_correctly y
  simp [h1.1, h1.2.1, h1.2.2, h2.1, h2.2]
  simp [Nat.repr_toNat]

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
      · simp [string_join_eq_concat]
        have : parse_apples_oranges (0.repr ++ " apples and " ++ n.repr ++ " oranges") = some (0, n) := 
          string_join_parse 0 n
        have : s ≠ 0.repr ++ " apples and " ++ n.repr ++ " oranges" := by
          intro contra
          rw [contra] at h
          rw [this] at h
          simp at h
        rw [← string_join_eq_concat]
        exact this.symm
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
          · have : parse_apples_oranges (x.repr ++ " apples and " ++ y.repr ++ " oranges") = some (x, y) := 
              string_join_parse x y
            have : s = x.repr ++ " apples and " ++ y.repr ++ " oranges" := by
              have : parse_apples_oranges s = some (x, y) := h
              sorry
            rw [← string_join_eq_concat]
            exact this
      · use 0
        constructor
        · simp [hle]
        · use 0, n
          constructor
          · simp
          · rw [← string_join_eq_concat]
            simp [Nat.repr]
            have : s = x.repr ++ " apples and " ++ y.repr ++ " oranges" := by
              sorry
            rw [this]
            simp
            have : x ≠ 0 ∨ y ≠ n := by
              by_contra contra
              push_neg at contra
              have : x + y = 0 + n := by rw [contra.1, contra.2]
              simp at this
              have : x + y ≤ n := by rw [this]
              contradiction
            cases this with
            | inl h1 => 
              simp [h1]
            | inr h2 => 
              simp [h2]