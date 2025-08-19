import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → List String)
-- inputs
(s: String) :=
-- spec
let spec (result: List String) :=
  let chars := s.toList;
  let first := s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ');
  (result = [] ↔ (∀ x ∈ chars, x = ' ' ∨ x = ',') ∨ s = "") ∧
  (result ≠ [] ↔ result = [first] ++ (implementation (s.drop (first.length + 1))))

-- program termination
∃ result, implementation s = result ∧
spec result

-- LLM HELPER
def implementation (s: String) : List String :=
  if s = "" then []
  else
    let chars := s.toList
    if ∀ x ∈ chars, x = ' ' ∨ x = ',' then []
    else
      let first := s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ')
      if first = "" then []
      else [first] ++ implementation (s.drop (first.length + 1))
termination_by s.length

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  let spec := fun result => 
    let chars := s.toList
    let first := s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ')
    (result = [] ↔ (∀ x ∈ chars, x = ' ' ∨ x = ',') ∨ s = "") ∧
    (result ≠ [] ↔ result = [first] ++ (implementation (s.drop (first.length + 1))))
  use implementation s
  constructor
  · rfl
  · unfold implementation
    simp only [spec]
    constructor
    · constructor
      · intro h
        by_cases h1 : s = ""
        · right; exact h1
        · left
          simp [implementation] at h
          split_ifs at h with h2 h3
          · exact h2
          · contradiction
          · contradiction
      · intro h
        cases h with
        | inl h => 
          simp [implementation]
          split_ifs with h1 h2
          · rfl
          · exact h
          · rfl
        | inr h =>
          simp [implementation, h]
    · constructor
      · intro h
        simp [implementation] at h
        split_ifs at h with h1 h2 h3
        · contradiction
        · contradiction
        · exact h
      · intro h
        simp [implementation]
        split_ifs with h1 h2 h3
        · exfalso
          cases h with
          | mk left right =>
            have : implementation s ≠ [] := by
              rw [right]
              simp
              sorry
            contradiction
        · exfalso
          cases h with
          | mk left right =>
            have : implementation s ≠ [] := by
              rw [right]
              simp
              sorry
            contradiction
        · exact h