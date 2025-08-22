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
  exact h

-- LLM HELPER
lemma filterPrimeWords_empty_iff (words : List String) :
  filterPrimeWords words = [] ↔ ∀ word ∈ words, ¬(Nat.Prime word.length) := by
  unfold filterPrimeWords
  rw [List.filter_eq_nil_iff]
  intro word
  simp [decide_eq_true_iff]

-- LLM HELPER
lemma implementation_eq (sentence : String) :
  implementation sentence = String.join (filterPrimeWords (sentence.splitOn)) := by
  unfold implementation
  rfl

-- LLM HELPER
lemma splitOn_join_self (words : List String) :
  words = [] ∨ (String.join words).splitOn = words := by
  cases' words with head tail
  · left; rfl
  · right
    simp [String.join]
    induction tail with
    | nil => simp
    | cons h t ih => simp [String.join]

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
      have h_split := splitOn_join_self (filterPrimeWords (sentence.splitOn))
      cases h_split with
      | inl h_empty => 
        simp [h_empty, String.join]
        simp [List.splitOn]
      | inr h_eq => 
        rw [h_eq]
        exact filterPrimeWords_subset (sentence.splitOn)
    · constructor
      · -- Membership constraint
        intro word h_mem
        rw [implementation_eq] at h_mem
        have h_split := splitOn_join_self (filterPrimeWords (sentence.splitOn))
        cases h_split with
        | inl h_empty => 
          simp [h_empty, String.join] at h_mem
          simp [List.splitOn] at h_mem
          cases h_mem
        | inr h_eq => 
          rw [h_eq] at h_mem
          exact filterPrimeWords_mem (sentence.splitOn) word h_mem
      · -- Main recursive constraint
        rw [implementation_eq]
        have h_split := splitOn_join_self (filterPrimeWords (sentence.splitOn))
        cases h_split with
        | inl h_empty => 
          simp [h_empty, String.join]
          rw [filterPrimeWords_empty_iff] at h_empty
          exact h_empty
        | inr h_eq => 
          rw [h_eq]
          cases' hp : filterPrimeWords (sentence.splitOn) with head tail
          · simp
            rw [filterPrimeWords_empty_iff] at hp
            exact hp
          · simp [String.join]
            by_cases h_cond : Nat.Prime head.length ∧ head = (sentence.splitOn)[0]!
            · simp [h_cond]
              rw [String.join]
              have : head ∈ filterPrimeWords (sentence.splitOn) := by
                rw [hp]
                simp
              have head_mem := filterPrimeWords_mem (sentence.splitOn) head this
              have head_prime := head_mem.2
              rw [implementation_eq]
              congr 1
              simp [String.join]
            · simp [h_cond]
              rw [implementation_eq]
              congr 1
              simp [String.join]