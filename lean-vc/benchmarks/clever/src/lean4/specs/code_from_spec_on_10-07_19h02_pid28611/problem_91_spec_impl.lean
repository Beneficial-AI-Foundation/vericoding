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
lemma drop_shorter (s: String) (i: Nat) : (s.drop i).length ≤ s.length := by
  unfold String.drop String.length
  simp only [List.length_drop]
  cases' h : i ≤ s.data.length with
  · exact Nat.sub_le _ _
  · simp [List.drop_length_le]

-- LLM HELPER
lemma findIdx_bound (s: String) (i: Nat) (h: s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') = some i) :
  i < s.length := by
  unfold String.length
  exact List.findIdx?_some_lt h

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
        have i_bound : i < s.length := findIdx_bound s i h_find
        have substring_shorter : (s.drop (i + 1)).length < s.length := by
          have : (s.drop (i + 1)).length ≤ s.length := drop_shorter s (i + 1)
          cases' h_eq : (s.drop (i + 1)).length = s.length with
          · unfold String.drop String.length at h_eq
            simp only [List.length_drop] at h_eq
            have : s.data.length ≤ i + 1 := by
              by_contra h_not
              push_neg at h_not
              have : s.data.length - (i + 1) > 0 := Nat.sub_pos_of_lt h_not
              rw [h_eq] at this
              exact not_lt_zero _ this
            have : i + 1 ≤ s.data.length := by
              rw [Nat.add_one_le_iff]
              exact i_bound
            omega
          · exact Nat.lt_of_le_of_ne this h_eq
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