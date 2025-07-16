import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: String → String)
-- inputs
(sentence: String) :=
-- spec
let spec (result: String) :=
let words := sentence.splitOn;
let result_words := result.splitOn;
  1 ≤ sentence.length → sentence.length ≤ 100 →
  sentence.all (fun x => Char.isAlpha x) →
  result_words.length ≤ words.length ∧
  (∀ word ∈ result_words, word ∈ words ∧ Nat.Prime word.length) ∧
  match result_words with
  | [] => ∀ word ∈ words, ¬(Nat.Prime word.length)
  | head :: tail => if Nat.Prime head.length ∧ head = words[0]! then String.join tail = impl (String.join (words.drop 1))
    else result = impl (String.join (words.drop 1))
-- program termination
∃ result, impl sentence = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def filterPrimeWords (words : List String) : List String :=
  words.filter (fun word => Nat.Prime word.length)

def implementation (sentence : String) : String := 
  let words := sentence.splitOn
  let primeWords := filterPrimeWords words
  String.join primeWords

-- LLM HELPER
lemma filterPrimeWords_subset (words : List String) : 
  (filterPrimeWords words).length ≤ words.length := by
  unfold filterPrimeWords
  apply List.length_filter_le

-- LLM HELPER
lemma filterPrimeWords_mem (words : List String) (word : String) :
  word ∈ filterPrimeWords words → word ∈ words ∧ Nat.Prime word.length := by
  unfold filterPrimeWords
  intro h
  rw [List.mem_filter] at h
  exact ⟨h.1, h.2⟩

-- LLM HELPER
lemma filterPrimeWords_empty_iff (words : List String) :
  filterPrimeWords words = [] ↔ ∀ word ∈ words, ¬(Nat.Prime word.length) := by
  unfold filterPrimeWords
  rw [List.filter_eq_nil_iff]
  simp

-- LLM HELPER
lemma implementation_eq (sentence : String) :
  implementation sentence = String.join (filterPrimeWords (sentence.splitOn)) := by
  unfold implementation
  rfl

-- LLM HELPER
lemma string_join_splitOn (s : String) : 
  s = "" ∨ (String.join [s]).splitOn = [s] := by
  by_cases h : s = ""
  · left; exact h
  · right
    simp [String.join]

theorem correctness
(sentence : String)
: problem_spec implementation sentence := by
  unfold problem_spec
  use implementation sentence
  constructor
  · rfl
  · intro h1 h2 h3
    constructor
    · -- Length constraint
      rw [implementation_eq]
      simp [String.join]
      exact filterPrimeWords_subset (sentence.splitOn)
    · constructor
      · -- Membership constraint
        intro word h_mem
        rw [implementation_eq] at h_mem
        simp [String.join] at h_mem
        exact filterPrimeWords_mem (sentence.splitOn) word h_mem
      · -- Main recursive constraint
        rw [implementation_eq]
        simp [String.join]
        cases' hp : filterPrimeWords (sentence.splitOn) with head tail
        · simp
          rw [filterPrimeWords_empty_iff] at hp
          exact hp
        · simp
          by_cases h_cond : Nat.Prime head.length ∧ head = (sentence.splitOn)[0]!
          · simp [h_cond]
            rw [implementation_eq]
            simp [String.join]
          · simp [h_cond]
            rw [implementation_eq]
            simp [String.join]