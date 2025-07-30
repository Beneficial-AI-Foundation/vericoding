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
      let j := i + 1;
      let substring := s.drop j;
      (if is_sentence_is_boredom substring then 1 else 0) + implementation_helper substring fuel
    | none =>
      if is_sentence_is_boredom s then 1 else 0

def implementation (s: String) : Nat := implementation_helper s s.length

-- LLM HELPER
lemma implementation_helper_correct (s: String) (fuel: Nat) (h: fuel ≥ s.length) :
  let spec (result : Nat) :=
    match s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
    | some i =>
      let j := i + 1;
      let substring := s.drop j;
      result = (if is_sentence_is_boredom substring then 1 else 0) + implementation substring
    | none =>
      result = if is_sentence_is_boredom s then 1 else 0
  spec (implementation_helper s fuel) := by
  induction fuel generalizing s
  case zero =>
    simp [implementation_helper]
    exfalso
    omega
  case succ fuel ih =>
    simp [implementation_helper]
    by_cases h_find : s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') = none
    · simp [h_find]
    · simp [h_find]
      cases' h_find_some : s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
      | none => simp at h_find
      | some i => 
        simp [h_find_some]
        simp [implementation]
        rfl

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · simp [implementation]
    have h : s.length ≥ s.length := le_refl _
    exact implementation_helper_correct s s.length h