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
lemma string_join_parse (x y : Nat) :
  parse_apples_oranges (String.join [x.repr, " apples and ", y.repr, " oranges"]) = some (x, y) := by
  simp [parse_apples_oranges, String.join]
  have h1 : (x.repr ++ " apples and " ++ y.repr ++ " oranges").splitOn " apples and " = 
    [x.repr, y.repr ++ " oranges"] := by
    have : ¬(" apples and " ≤ x.repr) := by
      simp [String.isPrefixOf]
      have : x.repr.length < " apples and ".length := by
        simp [String.length]
        have : x.repr.length ≤ 10 := by
          simp [Nat.repr]
          induction x with
          | zero => simp [Nat.repr]
          | succ n ih => simp [Nat.repr]; omega
        omega
      exact String.length_lt_isPrefixOf this
    simp [String.splitOn]
    simp [this]
  rw [h1]
  simp
  have h2 : (y.repr ++ " oranges").splitOn " oranges" = [y.repr, ""] := by
    simp [String.splitOn]
    have : ¬(" oranges" ≤ y.repr) := by
      simp [String.isPrefixOf]
      have : y.repr.length < " oranges".length := by
        simp [String.length]
        have : y.repr.length ≤ 10 := by
          simp [Nat.repr]
          induction y with
          | zero => simp [Nat.repr]
          | succ n ih => simp [Nat.repr]; omega
        omega
      exact String.length_lt_isPrefixOf this
    simp [this]
  rw [h2]
  simp
  have h3 : x.repr.toNat? = some x := by
    exact Nat.repr_toNat x
  have h4 : y.repr.toNat? = some y := by
    exact Nat.repr_toNat y
  rw [h3, h4]
  simp

-- LLM HELPER
lemma parse_implies_format (s : String) (x y : Nat) :
  parse_apples_oranges s = some (x, y) → 
  String.join [x.repr, " apples and ", y.repr, " oranges"] = s := by
  intro h
  simp [parse_apples_oranges] at h
  split at h
  · split at h
    · split at h
      · simp at h
        obtain ⟨hx, hy⟩ := h
        have : s = x.repr ++ " apples and " ++ y.repr ++ " oranges" := by
          simp [String.join]
          rw [← hx, ← hy]
          simp
        exact this
      · simp at h
    · simp at h
  · simp at h

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
      · simp [String.join]
        have : parse_apples_oranges (String.join [Nat.repr 0, " apples and ", Nat.repr n, " oranges"]) = some (0, n) := 
          string_join_parse 0 n
        have : s ≠ String.join [Nat.repr 0, " apples and ", Nat.repr n, " oranges"] := by
          intro contra
          rw [contra] at h
          rw [this] at h
          simp at h
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
          · exact parse_implies_format s x y h
      · use 0
        constructor
        · simp [hle]
        · use 0, n
          constructor
          · simp
          · have : s = String.join [x.repr, " apples and ", y.repr, " oranges"] := 
              parse_implies_format s x y h
            rw [this]
            simp [String.join]
            have : x ≠ 0 ∨ y ≠ n := by
              intro contra
              push_neg at contra
              have : x + y = 0 + n := by rw [contra.1, contra.2]
              simp at this
              have : x + y ≤ n := by rw [this]
              contradiction
            cases this with
            | inl h1 => simp [h1]
            | inr h2 => simp [h2]