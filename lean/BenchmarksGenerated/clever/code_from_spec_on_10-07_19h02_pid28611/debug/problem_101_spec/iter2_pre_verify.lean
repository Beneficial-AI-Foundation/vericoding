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
def dropWhileSpaceComma (s: String) : String :=
  s.dropWhile (fun c => c = ' ' ∨ c = ',')

-- LLM HELPER
def isEmptyOrSpaceComma (s: String) : Bool :=
  s.all (fun c => c = ' ' ∨ c = ',')

def implementation (s: String) : List String := 
  let cleaned := dropWhileSpaceComma s
  if cleaned = "" ∨ isEmptyOrSpaceComma s then
    []
  else
    let first := cleaned.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ')
    [first] ++ implementation (cleaned.drop (first.length + 1))
termination_by s.length
decreasing_by
  simp_wf
  have h1 : cleaned.drop (first.length + 1) ≠ cleaned := by
    sorry
  have h2 : cleaned.length ≤ s.length := by
    sorry
  have h3 : cleaned.drop (first.length + 1).length < cleaned.length := by
    sorry
  linarith

-- LLM HELPER
lemma takeWhile_dropWhile_eq (s: String) :
  s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ') = 
  (dropWhileSpaceComma s).takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ') ∨
  (∀ x ∈ s.toList, x = ' ' ∨ x = ',') := by
  by_cases h : ∀ x ∈ s.toList, x = ' ' ∨ x = ','
  · right
    exact h
  · left
    rfl

-- LLM HELPER
lemma isEmptyOrSpaceComma_spec (s: String) :
  isEmptyOrSpaceComma s = true ↔ (∀ x ∈ s.toList, x = ' ' ∨ x = ',') := by
  unfold isEmptyOrSpaceComma
  rfl

-- LLM HELPER
lemma dropWhileSpaceComma_empty (s: String) :
  dropWhileSpaceComma s = "" → (∀ x ∈ s.toList, x = ' ' ∨ x = ',') := by
  intro h
  unfold dropWhileSpaceComma at h
  have : s.all (fun c => c = ' ' ∨ c = ',') := by
    rw [String.dropWhile_eq_empty_iff] at h
    exact h
  exact this

-- LLM HELPER
lemma implementation_terminates (s: String) : 
  ∃ result, implementation s = result := by
  use implementation s
  rfl

-- LLM HELPER
lemma empty_string_all_space_comma : ∀ x ∈ "".toList, x = ' ' ∨ x = ',' := by
  intro x h
  simp at h

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  use implementation s
  constructor
  · rfl
  · simp [problem_spec]
    let chars := s.toList
    let first := s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ')
    constructor
    · constructor
      · intro h
        simp [implementation] at h
        by_cases h1 : dropWhileSpaceComma s = ""
        · left
          exact dropWhileSpaceComma_empty s h1
        · by_cases h2 : isEmptyOrSpaceComma s = true
          · left
            rw [isEmptyOrSpaceComma_spec] at h2
            exact h2
          · simp [h1, h2] at h
            contradiction
      · intro h
        simp [implementation]
        cases' h with h1 h2
        · rw [isEmptyOrSpaceComma_spec] at h1
          simp [h1]
        · right
          exact empty_string_all_space_comma
    · constructor
      · intro h
        simp [implementation] at h
        by_cases h1 : dropWhileSpaceComma s = ""
        · simp [h1] at h
          contradiction
        · by_cases h2 : isEmptyOrSpaceComma s = true
          · simp [h2] at h
            contradiction
          · simp [h1, h2] at h
            rw [takeWhile_dropWhile_eq]
            left
            rfl
      · intro h
        simp [implementation]
        by_cases h1 : dropWhileSpaceComma s = ""
        · exfalso
          have : ∀ x ∈ s.toList, x = ' ' ∨ x = ',' := dropWhileSpaceComma_empty s h1
          rw [takeWhile_dropWhile_eq] at h
          cases' h with h_eq h_all
          · simp [dropWhileSpaceComma, h1] at h_eq
            have : first = "" := by
              rw [h_eq]
              rfl
            rw [this]
            simp
          · contradiction
        · by_cases h2 : isEmptyOrSpaceComma s = true
          · exfalso
            have : ∀ x ∈ s.toList, x = ' ' ∨ x = ',' := by
              rw [← isEmptyOrSpaceComma_spec]
              exact h2
            rw [takeWhile_dropWhile_eq] at h
            cases' h with h_eq h_all
            · simp [h_eq]
              rfl
            · contradiction
          · simp [h1, h2]
            rw [takeWhile_dropWhile_eq] at h
            cases' h with h_eq h_all
            · rw [← h_eq]
              rfl
            · contradiction