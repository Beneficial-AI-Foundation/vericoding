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
let words := sentence.split (· = ' ');
let result_words := result.split (· = ' ');
  1 ≤ sentence.length → sentence.length ≤ 100 →
  sentence.all (fun x => x.isAlpha || x = ' ') →
  result_words.length ≤ words.length ∧
  (∀ word ∈ result_words, word ∈ words ∧ Nat.Prime word.length) ∧
  match result_words with
  | [] => ∀ word ∈ words, ¬(Nat.Prime word.length)
  | head :: tail => if Nat.Prime head.length ∧ head = words[0]! then String.join " " tail = impl (String.join " " (words.drop 1))
    else result = impl (String.join " " (words.drop 1))
-- program termination
∃ result, impl sentence = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def filterPrimeWords (words : List String) : List String :=
  words.filter (fun word => Nat.Prime word.length)

def implementation (sentence : String) : String := 
  let words := sentence.split (· = ' ')
  let primeWords := filterPrimeWords words
  String.join " " primeWords

-- LLM HELPER
lemma filterPrimeWords_subset (words : List String) : 
  ∀ word ∈ filterPrimeWords words, word ∈ words := by
  intro word h
  exact List.mem_of_mem_filter h

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

-- LLM HELPER
lemma prime_iff_not_prime (n : Nat) : Nat.Prime n ↔ ¬¬Nat.Prime n := by
  simp

theorem correctness
(sentence : String)
: problem_spec implementation sentence := by
  unfold problem_spec
  use implementation sentence
  constructor
  · rfl
  · intro h1 h2 h3
    constructor
    · exact filterPrimeWords_length_le (sentence.split (· = ' '))
    · constructor
      · intro word h
        constructor
        · exact filterPrimeWords_subset (sentence.split (· = ' ')) word h
        · exact filterPrimeWords_all_prime (sentence.split (· = ' ')) word h
      · simp [implementation]
        cases' filterPrimeWords (sentence.split (· = ' ')) with head tail
        · intro word h
          rw [filterPrimeWords] at h
          simp at h
          exact h
        · simp