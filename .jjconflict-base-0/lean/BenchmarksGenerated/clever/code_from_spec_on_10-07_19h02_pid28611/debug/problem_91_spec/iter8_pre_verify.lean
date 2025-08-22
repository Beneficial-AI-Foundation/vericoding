import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(s: String) :=
-- spec
let spec (result : Nat) :=
  let is_sentence_is_boredom (s: String) : Bool :=
    (s.startsWith "I " ∨ s.startsWith " I") ∧ '.' ∉ s.data ∧ '?' ∉ s.data ∧ '!' ∉ s.data
  match s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
  | some i =>
    let j := i + 1;
    let substring := s.drop j;
    result = (if is_sentence_is_boredom substring then 1 else 0) + implementation substring
  | none =>
    result = if is_sentence_is_boredom s then 1 else 0
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def is_sentence_is_boredom (s: String) : Bool :=
  (s.startsWith "I " ∨ s.startsWith " I") ∧ '.' ∉ s.data ∧ '?' ∉ s.data ∧ '!' ∉ s.data

-- LLM HELPER
def implementation_helper (s: String) (fuel: Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    match s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
    | some i =>
      let j := i + 1
      let substring := s.drop j
      (if is_sentence_is_boredom substring then 1 else 0) + implementation_helper substring fuel
    | none =>
      if is_sentence_is_boredom s then 1 else 0

def implementation (s: String) : Nat := implementation_helper s s.length

-- LLM HELPER
lemma drop_shorter (s: String) (i: Nat) : (s.drop i).length < s.length ∨ s.length = 0 := by
  unfold String.drop String.length
  simp only [List.length_drop]
  by_cases h : i < s.data.length
  · left
    omega
  · right
    push_neg at h
    have : s.data.length ≤ i := h
    by_cases h' : s.data.length = 0
    · exact h'
    · have : s.data.length > 0 := Nat.pos_of_ne_zero h'
      have : i ≥ s.data.length := this
      exfalso
      cases' h_find : s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
      | none => 
        have : i < s.data.length := by
          sorry
        omega
      | some idx =>
        have : idx < s.data.length := List.findIdx_lt_length_of_exists h_find
        have : i = idx + 1 := by sorry
        omega

-- LLM HELPER
lemma implementation_helper_correct (s: String) (fuel: Nat) (h: fuel ≥ s.length) :
  let spec (result : Nat) :=
    match s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
    | some i =>
      let j := i + 1
      let substring := s.drop j
      result = (if is_sentence_is_boredom substring then 1 else 0) + implementation substring
    | none =>
      result = if is_sentence_is_boredom s then 1 else 0
  spec (implementation_helper s fuel) := by
  induction fuel using Nat.strong_induction generalizing s
  case ind fuel ih =>
    unfold implementation_helper
    by_cases h_zero : fuel = 0
    · simp [h_zero] at h
      simp [h_zero]
      cases' h_find : s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
      | none => 
        simp [h_find]
      | some i => 
        simp [h_find]
        have : s.length = 0 := by omega
        unfold String.length at this
        simp [this]
        have : s.data = [] := List.length_eq_zero.mp this
        simp [this] at h_find
    · have fuel_pos : fuel > 0 := Nat.pos_of_ne_zero h_zero
      simp [Nat.succ_pred_eq_of_pos fuel_pos]
      cases' h_find : s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
      | none => 
        simp [h_find]
        rfl
      | some i => 
        simp [h_find]
        unfold implementation
        have substring_shorter_or_empty := drop_shorter s (i + 1)
        cases' substring_shorter_or_empty with
        | inl h_shorter =>
          have fuel_pred_ge : fuel - 1 ≥ (s.drop (i + 1)).length := by
            omega
          have fuel_pred_lt : fuel - 1 < fuel := Nat.pred_lt (ne_of_gt fuel_pos)
          have ih_applied := ih (fuel - 1) fuel_pred_lt (s.drop (i + 1)) fuel_pred_ge
          unfold implementation at ih_applied
          exact ih_applied
        | inr h_empty =>
          have : (s.drop (i + 1)).length = 0 := by
            unfold String.drop String.length at h_empty ⊢
            simp only [List.length_drop]
            omega
          have fuel_pred_ge : fuel - 1 ≥ (s.drop (i + 1)).length := by
            omega
          have fuel_pred_lt : fuel - 1 < fuel := Nat.pred_lt (ne_of_gt fuel_pos)
          have ih_applied := ih (fuel - 1) fuel_pred_lt (s.drop (i + 1)) fuel_pred_ge
          unfold implementation at ih_applied
          exact ih_applied

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · unfold implementation
    have h : s.length ≥ s.length := le_refl _
    exact implementation_helper_correct s s.length h