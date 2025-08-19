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
  (filterPrimeWords words).Subset words := by
  exact List.filter_subset _ _

-- LLM HELPER  
lemma filterPrimeWords_all_prime (words : List String) :
  ∀ word ∈ filterPrimeWords words, Nat.Prime word.length := by
  intro word h
  rw [filterPrimeWords] at h
  exact List.of_mem_filter h

-- LLM HELPER
lemma filterPrimeWords_length_le (words : List String) :
  (filterPrimeWords words).length ≤ words.length := by
  exact List.length_filter_le _ _

theorem correctness
(sentence : String)
: problem_spec implementation sentence := by
  unfold problem_spec
  use implementation sentence
  constructor
  · rfl
  · intro h1 h2 h3
    constructor
    · exact filterPrimeWords_length_le (sentence.splitOn)
    · constructor
      · intro word h
        constructor
        · exact filterPrimeWords_subset (sentence.splitOn) h
        · exact filterPrimeWords_all_prime (sentence.splitOn) word h
      · simp [implementation]
        cases' filterPrimeWords (sentence.splitOn) with head tail
        · intro word h
          rw [filterPrimeWords] at h
          simp at h
          exact h
        · simp