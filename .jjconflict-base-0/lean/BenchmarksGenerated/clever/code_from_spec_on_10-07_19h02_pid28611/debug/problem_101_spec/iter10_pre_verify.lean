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
  have h2 : cleaned.length ≤ s.length := by
    unfold cleaned
    exact String.length_dropWhile_le s (fun c => c = ' ' ∨ c = ',')
  have h3 : 0 < cleaned.length := by
    apply String.length_pos_iff_ne_empty.mpr
    simp [cleaned]
    intro h
    have : isEmptyOrSpaceComma s = true := by
      rw [isEmptyOrSpaceComma]
      rw [String.all_iff]
      simp [decide_eq_true_iff]
      exact dropWhileSpaceComma_empty s h
    simp at this
  have h4 : cleaned.drop (first.length + 1).length < cleaned.length := by
    rw [String.length_drop]
    cases' Nat.lt_or_le (first.length + 1) cleaned.length with h h
    · exact Nat.sub_lt h3 (Nat.succ_pos _)
    · rw [Nat.sub_eq_zero_of_le h]
      exact h3
  have h5 : cleaned.drop (first.length + 1).length < s.length := by
    calc cleaned.drop (first.length + 1).length 
      < cleaned.length := h4
      _ ≤ s.length := h2
  exact h5

-- LLM HELPER
lemma String.length_dropWhile_le (s: String) (p: Char → Bool) :
  (s.dropWhile p).length ≤ s.length := by
  rw [String.length_eq_toList_length, String.length_eq_toList_length]
  rw [String.dropWhile_toList]
  exact List.length_dropWhile_le _ _

-- LLM HELPER
lemma String.dropWhile_toList (s: String) (p: Char → Bool) :
  (s.dropWhile p).toList = List.dropWhile p s.toList := by
  rfl

-- LLM HELPER
lemma String.length_drop (s: String) (n: Nat) :
  (s.drop n).length = s.length - n := by
  rw [String.length_eq_toList_length, String.length_eq_toList_length]
  rw [String.drop_toList]
  exact List.length_drop _ _

-- LLM HELPER
lemma String.drop_toList (s: String) (n: Nat) :
  (s.drop n).toList = List.drop n s.toList := by
  rfl

-- LLM HELPER
lemma dropWhileSpaceComma_empty (s: String) :
  dropWhileSpaceComma s = "" → (∀ x ∈ s.toList, x = ' ' ∨ x = ',') := by
  intro h
  unfold dropWhileSpaceComma at h
  rw [String.dropWhile_eq_empty_iff] at h
  rw [String.all_iff] at h
  simp [decide_eq_true_iff] at h
  exact h

-- LLM HELPER
lemma String.dropWhile_eq_empty_iff (s: String) (p: Char → Bool) :
  s.dropWhile p = "" ↔ s.all p := by
  rw [String.dropWhile_eq_empty_iff_all]

-- LLM HELPER
lemma String.dropWhile_eq_empty_iff_all (s: String) (p: Char → Bool) :
  s.dropWhile p = "" ↔ s.all p := by
  rw [String.eq_empty_iff_toList_eq_nil]
  rw [String.dropWhile_toList]
  rw [List.dropWhile_eq_nil_iff]
  rw [← String.all_iff]
  simp

-- LLM HELPER
lemma String.eq_empty_iff_toList_eq_nil (s: String) :
  s = "" ↔ s.toList = [] := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    rw [← String.toList_inj]
    rw [h]
    rfl

-- LLM HELPER
lemma takeWhile_eq_when_not_all_space_comma (s: String) :
  ¬(∀ x ∈ s.toList, x = ' ' ∨ x = ',') →
  s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ') = 
  (dropWhileSpaceComma s).takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ') := by
  intro h
  unfold dropWhileSpaceComma
  rw [String.takeWhile_dropWhile_comm]
  intro c
  simp [decide_eq_true_iff]
  constructor
  · intro h1
    push_neg at h1
    exact Or.inl h1
  · intro h2
    cases' h2 with h2 h2
    · exact h2
    · exact h2

-- LLM HELPER
lemma String.takeWhile_dropWhile_comm (s: String) (p q: Char → Bool) :
  (∀ c, p c ↔ ¬q c) → 
  s.takeWhile p = (s.dropWhile q).takeWhile p := by
  intro h
  rw [← String.toList_inj]
  rw [String.takeWhile_toList]
  rw [String.dropWhile_toList]
  rw [String.takeWhile_toList]
  rw [List.takeWhile_dropWhile_comm]
  exact h

-- LLM HELPER
lemma String.takeWhile_toList (s: String) (p: Char → Bool) :
  (s.takeWhile p).toList = List.takeWhile p s.toList := by
  rfl

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
            rw [isEmptyOrSpaceComma] at h2
            rw [String.all_iff] at h2
            simp [decide_eq_true_iff] at h2
            exact h2
          · simp [h1, h2] at h
      · intro h
        simp [implementation]
        cases' h with h1 h2
        · rw [isEmptyOrSpaceComma]
          rw [String.all_iff]
          simp [decide_eq_true_iff]
          right
          exact h1
        · left
          unfold dropWhileSpaceComma
          rw [String.dropWhile_eq_empty_iff]
          rw [String.all_iff]
          simp [h2, decide_eq_true_iff]
    · constructor
      · intro h
        simp [implementation] at h
        by_cases h1 : dropWhileSpaceComma s = ""
        · exfalso
          have : ∀ x ∈ s.toList, x = ' ' ∨ x = ',' := dropWhileSpaceComma_empty s h1
          have : first = "" := by
            simp [first]
            rw [String.takeWhile_eq_empty_iff]
            right
            intro x hx
            simp
            exact this x hx
          rw [this] at h
          simp at h
        · by_cases h2 : isEmptyOrSpaceComma s = true
          · exfalso
            have : ∀ x ∈ s.toList, x = ' ' ∨ x = ',' := by
              rw [isEmptyOrSpaceComma] at h2
              rw [String.all_iff] at h2
              simp [decide_eq_true_iff] at h2
              exact h2
            have : first = "" := by
              simp [first]
              rw [String.takeWhile_eq_empty_iff]
              right
              intro x hx
              simp
              exact this x hx
            rw [this] at h
            simp at h
          · simp [h1, h2]
            rw [takeWhile_eq_when_not_all_space_comma]
            rw [isEmptyOrSpaceComma] at h2
            rw [String.all_iff] at h2
            simp [decide_eq_true_iff] at h2
            exact h2
      · intro h
        simp [implementation]
        by_cases h1 : dropWhileSpaceComma s = ""
        · exfalso
          have : ∀ x ∈ s.toList, x = ' ' ∨ x = ',' := dropWhileSpaceComma_empty s h1
          have : first = "" := by
            simp [first]
            rw [String.takeWhile_eq_empty_iff]
            right
            intro x hx
            simp
            exact this x hx
          rw [this] at h
          simp at h
        · by_cases h2 : isEmptyOrSpaceComma s = true
          · exfalso
            have : ∀ x ∈ s.toList, x = ' ' ∨ x = ',' := by
              rw [isEmptyOrSpaceComma] at h2
              rw [String.all_iff] at h2
              simp [decide_eq_true_iff] at h2
              exact h2
            have : first = "" := by
              simp [first]
              rw [String.takeWhile_eq_empty_iff]
              right
              intro x hx
              simp
              exact this x hx
            rw [this] at h
            simp at h
          · simp [h1, h2]
            rw [takeWhile_eq_when_not_all_space_comma]
            rw [isEmptyOrSpaceComma] at h2
            rw [String.all_iff] at h2
            simp [decide_eq_true_iff] at h2
            exact h2

-- LLM HELPER
lemma String.takeWhile_eq_empty_iff (s: String) (p: Char → Bool) :
  s.takeWhile p = "" ↔ s = "" ∨ ∀ x ∈ s.toList, ¬p x := by
  rw [String.eq_empty_iff_toList_eq_nil]
  rw [String.takeWhile_toList]
  rw [List.takeWhile_eq_nil_iff]
  constructor
  · intro h
    cases' h with h1 h2
    · left
      exact String.eq_empty_iff_toList_eq_nil.mpr h1
    · right
      exact h2
  · intro h
    cases' h with h1 h2
    · left
      exact String.eq_empty_iff_toList_eq_nil.mp h1
    · right
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
      exact ih
    · simp [ha]
      have : p a := by
        rw [h]
        exact ha
      simp [this]
      exact ih