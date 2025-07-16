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
    unfold cleaned first
    apply String.drop_ne_self
    · simp
    · have : cleaned ≠ "" := by
        simp [cleaned]
        intro h
        have : isEmptyOrSpaceComma s = true := by
          rw [isEmptyOrSpaceComma_spec]
          exact dropWhileSpaceComma_empty s h
        simp at this
      exact String.length_pos_iff_ne_empty.mpr this
  have h2 : cleaned.length ≤ s.length := by
    unfold cleaned
    apply String.dropWhile_length_le
  have h3 : cleaned.drop (first.length + 1).length < cleaned.length := by
    apply String.drop_length_lt
    · simp
    · have : cleaned ≠ "" := by
        simp [cleaned]
        intro h
        have : isEmptyOrSpaceComma s = true := by
          rw [isEmptyOrSpaceComma_spec]
          exact dropWhileSpaceComma_empty s h
        simp at this
      exact String.length_pos_iff_ne_empty.mpr this
  have h4 : cleaned.drop (first.length + 1).length < s.length := by
    calc cleaned.drop (first.length + 1).length 
      < cleaned.length := h3
      _ ≤ s.length := h2
  exact h4

-- LLM HELPER
lemma String.dropWhile_length_le (s: String) (p: Char → Bool) :
  (s.dropWhile p).length ≤ s.length := by
  have : s.dropWhile p = s.toList.dropWhile p |>.asString := by
    rw [String.dropWhile_toList]
  rw [this, String.length_asString]
  exact List.length_dropWhile_le _ _

-- LLM HELPER
lemma String.drop_length_lt (s: String) (n: Nat) :
  n > 0 → s.length > 0 → (s.drop n).length < s.length := by
  intro hn hs
  rw [String.length_drop]
  exact Nat.sub_lt hs hn

-- LLM HELPER
lemma String.drop_ne_self (s: String) (n: Nat) :
  n > 0 → s.length > 0 → s.drop n ≠ s := by
  intro hn hs h
  have : (s.drop n).length = s.length := by rw [h]
  have : (s.drop n).length < s.length := String.drop_length_lt s n hn hs
  linarith

-- LLM HELPER
lemma isEmptyOrSpaceComma_spec (s: String) :
  isEmptyOrSpaceComma s = true ↔ (∀ x ∈ s.toList, x = ' ' ∨ x = ',') := by
  unfold isEmptyOrSpaceComma
  rw [String.all_iff]
  simp [decide_eq_true_iff]

-- LLM HELPER
lemma dropWhileSpaceComma_empty (s: String) :
  dropWhileSpaceComma s = "" → (∀ x ∈ s.toList, x = ' ' ∨ x = ',') := by
  intro h
  unfold dropWhileSpaceComma at h
  rw [String.dropWhile_eq_empty_iff] at h
  rw [← isEmptyOrSpaceComma_spec] at h
  exact h

-- LLM HELPER
lemma String.dropWhile_eq_empty_iff (s: String) (p: Char → Bool) :
  s.dropWhile p = "" ↔ s.all p := by
  rw [String.dropWhile_toList, String.all_iff]
  constructor
  · intro h
    simp [String.asString_eq_empty] at h
    exact List.dropWhile_eq_nil_iff.mp h
  · intro h
    simp [String.asString_eq_empty]
    exact List.dropWhile_eq_nil_iff.mpr h

-- LLM HELPER
lemma takeWhile_eq_when_not_all_space_comma (s: String) :
  ¬(∀ x ∈ s.toList, x = ' ' ∨ x = ',') →
  s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ') = 
  (dropWhileSpaceComma s).takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ') := by
  intro h
  unfold dropWhileSpaceComma
  rw [String.takeWhile_dropWhile_comm]

-- LLM HELPER
lemma String.takeWhile_dropWhile_comm (s: String) :
  s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ') = 
  (s.dropWhile (fun c => c = ' ' ∨ c = ',')).takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ') := by
  rw [String.takeWhile_toList, String.dropWhile_toList, String.takeWhile_toList]
  simp only [String.asString_toList]
  rw [List.takeWhile_dropWhile_comm]
  intro c
  simp

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
      · intro h
        simp [implementation]
        cases' h with h1 h2
        · rw [isEmptyOrSpaceComma_spec] at h1
          right
          exact h1
        · left
          unfold dropWhileSpaceComma
          rw [String.dropWhile_eq_empty_iff]
          rw [← isEmptyOrSpaceComma_spec]
          simp [h2]
    · constructor
      · intro h
        simp [implementation] at h
        by_cases h1 : dropWhileSpaceComma s = ""
        · simp [h1] at h
        · by_cases h2 : isEmptyOrSpaceComma s = true
          · simp [h2] at h
          · simp [h1, h2] at h
            rw [takeWhile_eq_when_not_all_space_comma]
            · rw [← isEmptyOrSpaceComma_spec] at h2
              simp at h2
              exact h2
      · intro h
        simp [implementation]
        by_cases h1 : dropWhileSpaceComma s = ""
        · exfalso
          have : ∀ x ∈ s.toList, x = ' ' ∨ x = ',' := dropWhileSpaceComma_empty s h1
          rw [← takeWhile_eq_when_not_all_space_comma] at h
          · have : first = "" := by
              simp [first]
              rw [String.takeWhile_eq_empty_iff]
              right
              intro x hx
              simp
              exact this x hx
            rw [this] at h
            simp at h
          · exact this
        · by_cases h2 : isEmptyOrSpaceComma s = true
          · exfalso
            have : ∀ x ∈ s.toList, x = ' ' ∨ x = ',' := by
              rw [← isEmptyOrSpaceComma_spec]
              exact h2
            rw [← takeWhile_eq_when_not_all_space_comma] at h
            · have : first = "" := by
                simp [first]
                rw [String.takeWhile_eq_empty_iff]
                right
                intro x hx
                simp
                exact this x hx
              rw [this] at h
              simp at h
            · exact this
          · simp [h1, h2]
            rw [takeWhile_eq_when_not_all_space_comma]
            rw [← isEmptyOrSpaceComma_spec] at h2
            simp at h2
            exact h2

-- LLM HELPER
lemma String.takeWhile_eq_empty_iff (s: String) (p: Char → Bool) :
  s.takeWhile p = "" ↔ s = "" ∨ ∀ x ∈ s.toList, ¬p x := by
  rw [String.takeWhile_toList]
  constructor
  · intro h
    simp [String.asString_eq_empty] at h
    cases' List.takeWhile_eq_nil_iff.mp h with h1 h2
    · left
      exact String.toList_eq_nil_iff.mp h1
    · right
      exact h2
  · intro h
    cases' h with h1 h2
    · simp [String.asString_eq_empty]
      rw [List.takeWhile_eq_nil_iff]
      left
      exact String.toList_eq_nil_iff.mpr h1
    · simp [String.asString_eq_empty]
      rw [List.takeWhile_eq_nil_iff]
      right
      exact h2

-- LLM HELPER
lemma List.takeWhile_dropWhile_comm {α : Type*} (l : List α) (p q : α → Bool) :
  (∀ x, p x ↔ ¬q x) → l.takeWhile p = (l.dropWhile q).takeWhile p := by
  intro h
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.takeWhile_cons, List.dropWhile_cons]
    by_cases ha : q a
    · simp [ha]
      have : ¬p a := by
        rw [h]
        exact fun h => h ha
      simp [this]
    · simp [ha]
      have : p a := by
        rw [h]
        exact ha
      simp [this]
      exact ih