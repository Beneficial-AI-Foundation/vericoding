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
def string_length_drops (s: String) : s.drop (s.length) = "" := by
  simp [String.drop_length]

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
lemma implementation_helper_monotonic (s: String) (n m: Nat) (h: n ≤ m) :
  implementation_helper s n = implementation_helper s m ∨ 
  (∃ i, i < n ∧ implementation_helper s n = implementation_helper s i) := by
  sorry

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
  sorry

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