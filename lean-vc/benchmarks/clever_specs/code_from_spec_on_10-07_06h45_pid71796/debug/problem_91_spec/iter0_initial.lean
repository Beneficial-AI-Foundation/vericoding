import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
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
def find_punctuation_index (s: String) : Option Nat :=
  s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!')

def implementation (s: String) : Nat :=
  match find_punctuation_index s with
  | some i =>
    let j := i + 1
    let substring := s.drop j
    (if is_sentence_is_boredom substring then 1 else 0) + implementation substring
  | none =>
    if is_sentence_is_boredom s then 1 else 0

-- LLM HELPER
theorem implementation_matches_spec (s: String) :
  let spec (result : Nat) :=
    match s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
    | some i =>
      let j := i + 1;
      let substring := s.drop j;
      result = (if is_sentence_is_boredom substring then 1 else 0) + implementation substring
    | none =>
      result = if is_sentence_is_boredom s then 1 else 0
  spec (implementation s) := by
  simp [implementation, find_punctuation_index, is_sentence_is_boredom]
  cases h : s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!')
  case none => simp
  case some i => simp

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · exact implementation_matches_spec s