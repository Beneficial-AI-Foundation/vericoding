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
def isEmptyOrSeparators (s: String) : Bool :=
  s.toList.all (fun c => c = ' ' ∨ c = ',')

def implementation (s: String) : List String := 
  if s = "" ∨ isEmptyOrSeparators s then 
    []
  else
    let first := s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ')
    [first] ++ (implementation (s.drop (first.length + 1)))

-- LLM HELPER
theorem isEmptyOrSeparators_correct (s: String) :
  isEmptyOrSeparators s = true ↔ (∀ x ∈ s.toList, x = ' ' ∨ x = ',') := by
  simp [isEmptyOrSeparators, List.all_eq_true]

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  let spec := fun result => 
    let chars := s.toList;
    let first := s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ');
    (result = [] ↔ (∀ x ∈ chars, x = ' ' ∨ x = ',') ∨ s = "") ∧
    (result ≠ [] ↔ result = [first] ++ (implementation (s.drop (first.length + 1))))
  
  use implementation s
  constructor
  · rfl
  · unfold spec
    simp [implementation]
    constructor
    · constructor
      · intro h
        by_cases h1 : s = ""
        · right; exact h1
        · by_cases h2 : isEmptyOrSeparators s
          · left
            rw [isEmptyOrSeparators_correct] at h2
            exact h2
          · simp [h1, h2] at h
      · intro h
        cases h with
        | inl h => 
          simp [isEmptyOrSeparators_correct.mpr h]
        | inr h => 
          simp [h]
    · constructor
      · intro h
        by_cases h1 : s = ""
        · simp [h1] at h
        · by_cases h2 : isEmptyOrSeparators s
          · simp [h2] at h
          · simp [h1, h2] at h
            exact h
      · intro h
        by_cases h1 : s = ""
        · simp [h1] at h
        · by_cases h2 : isEmptyOrSeparators s
          · simp [h2] at h
          · simp [h1, h2]
            exact h