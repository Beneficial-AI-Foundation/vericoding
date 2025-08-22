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
    linarith
  have h2 : cleaned.length ≤ s.length := by
    unfold cleaned
    apply String.dropWhile_length_le
  have h3 : cleaned.drop (first.length + 1).length < cleaned.length := by
    unfold cleaned first
    apply String.drop_length_lt
    simp
  linarith

-- LLM HELPER
lemma String.dropWhile_length_le (s: String) (p: Char → Bool) :
  (s.dropWhile p).length ≤ s.length := by
  induction s using String.inductionOn with
  | h0 => simp
  | hi c s ih =>
    simp only [String.dropWhile_cons]
    by_cases h : p c
    · simp [h]
      exact Nat.le_trans ih (Nat.le_succ _)
    · simp [h]

-- LLM HELPER
lemma String.drop_length_lt (s: String) (n: Nat) :
  n > 0 → s.length > 0 → (s.drop n).length < s.length := by
  intro hn hs
  rw [String.length_drop]
  apply Nat.sub_lt hs hn

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
  rw [String.all_eq_true]
  constructor
  · intro h x hx
    have := h x hx
    simp at this
    exact this
  · intro h x hx
    simp
    exact h x hx

-- LLM HELPER
lemma dropWhileSpaceComma_empty (s: String) :
  dropWhileSpaceComma s = "" → (∀ x ∈ s.toList, x = ' ' ∨ x = ',') := by
  intro h
  unfold dropWhileSpaceComma at h
  rw [String.dropWhile_eq_empty_iff] at h
  exact h

-- LLM HELPER
lemma String.dropWhile_eq_empty_iff (s: String) (p: Char → Bool) :
  s.dropWhile p = "" ↔ s.all p := by
  constructor
  · intro h
    induction s using String.inductionOn with
    | h0 => simp
    | hi c s ih =>
      simp only [String.dropWhile_cons] at h
      by_cases hc : p c
      · simp [hc] at h
        simp [String.all_cons, hc, ih h]
      · simp [hc] at h
        contradiction
  · intro h
    induction s using String.inductionOn with
    | h0 => simp
    | hi c s ih =>
      simp only [String.all_cons] at h
      simp only [String.dropWhile_cons]
      simp [h.1]
      exact ih h.2

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
  induction s using String.inductionOn with
  | h0 => simp
  | hi c s ih =>
    by_cases h : c = ' ' ∨ c = ','
    · simp [String.takeWhile_cons, String.dropWhile_cons, h]
      rw [Bool.not_eq_true]
      simp [h]
    · simp [String.takeWhile_cons, String.dropWhile_cons, h]
      push_neg at h
      simp [h]
      rw [ih]

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
              intro x hx
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
                intro x hx
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
  constructor
  · intro h
    induction s using String.inductionOn with
    | h0 => left; rfl
    | hi c s ih =>
      right
      simp only [String.takeWhile_cons] at h
      by_cases hc : p c
      · simp [hc] at h
        have : s.takeWhile p = "" := by
          rw [String.cons_head_tail] at h
          simp at h
          exact h
        cases' ih this with h1 h2
        · simp [String.toList_cons, h1]
          exact fun _ => hc
        · simp [String.toList_cons]
          intro x hx
          cases' hx with h3 h4
          · rw [← h3]
            exact hc
          · exact h2 x h4
      · simp [String.toList_cons]
        intro x hx
        cases' hx with h3 h4
        · rw [← h3]
          exact hc
        · exact fun _ => hc
  · intro h
    cases' h with h1 h2
    · rw [h1]
      simp
    · induction s using String.inductionOn with
      | h0 => simp
      | hi c s ih =>
        simp only [String.takeWhile_cons]
        have : ¬p c := by
          apply h2
          simp [String.toList_cons]
        simp [this]