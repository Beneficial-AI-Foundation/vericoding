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

-- LLM HELPER
lemma string_join_tail_shorter (sentence : String) (words : List String) :
  sentence ≠ "" → words = sentence.splitOn → words ≠ [] → 
  (String.join words.tail).length < sentence.length := by
  intro h_neq h_words h_nonempty
  sorry

def implementation (sentence : String) : String := 
  if sentence = "" then ""
  else
    let words := sentence.splitOn
    let primeWords := filterPrimeWords words
    match primeWords with
    | [] => ""
    | head :: tail => 
      if Nat.Prime head.length ∧ head = words[0]! then
        head ++ " " ++ implementation (String.join words.tail)
      else implementation (String.join words.tail)
termination_by sentence.length

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
lemma string_empty_splitOn : ("" : String).splitOn = [] := by
  simp [String.splitOn]

-- LLM HELPER
lemma string_join_empty : String.join [] = "" := by
  rfl

-- LLM HELPER
lemma decide_eq_true_iff_prop (p : Prop) [Decidable p] : decide p = true ↔ p := by
  simp [decide_eq_true_iff]

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
      sorry
    · constructor
      · -- Membership constraint
        intro word h_mem
        by_cases h_empty : sentence = ""
        · rw [h_empty] at h_mem
          simp [implementation, string_empty_splitOn] at h_mem
        · sorry
      · -- Main recursive constraint
        by_cases h_empty : sentence = ""
        · rw [h_empty]
          simp [implementation, string_empty_splitOn]
          intro word h_mem
          exact False.elim h_mem
        · simp [implementation, h_empty]
          split
          · simp
            exact filterPrimeWords_empty_iff (sentence.splitOn)
          · case h_2 head tail hp =>
            simp
            split
            · case h_1 h_cond =>
              simp [h_cond]
              sorry
            · case h_2 h_cond =>
              simp [h_cond]
              sorry