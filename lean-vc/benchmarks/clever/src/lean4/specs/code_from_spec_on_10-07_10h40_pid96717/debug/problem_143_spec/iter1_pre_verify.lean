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
def filter_prime_length_words (words : List String) : List String :=
  words.filter (fun word => Nat.Prime word.length)

def implementation (sentence : String) : String := 
  let words := sentence.splitOn
  let prime_words := filter_prime_length_words words
  String.join prime_words

-- LLM HELPER
lemma filter_subset {α : Type*} (p : α → Bool) (l : List α) : 
  (l.filter p).length ≤ l.length := by
  induction l with
  | nil => simp [List.filter]
  | cons head tail ih => 
    simp [List.filter]
    split_ifs with h
    · simp; exact Nat.succ_le_succ ih
    · exact Nat.le_succ_of_le ih

-- LLM HELPER  
lemma filter_mem {α : Type*} (p : α → Bool) (l : List α) :
  ∀ x ∈ l.filter p, x ∈ l := by
  intro x hx
  exact List.mem_of_mem_filter hx

-- LLM HELPER
lemma filter_property {α : Type*} (p : α → Bool) (l : List α) :
  ∀ x ∈ l.filter p, p x = true := by
  intro x hx
  exact List.of_mem_filter hx

theorem correctness
(sentence : String)
: problem_spec implementation sentence := by
  unfold problem_spec
  let words := sentence.splitOn
  let prime_words := filter_prime_length_words words
  let result := String.join prime_words
  use result
  constructor
  · rfl
  · intro h1 h2 h3
    let result_words := result.splitOn
    constructor
    · apply filter_subset
    · constructor
      · intro word hw
        constructor
        · apply filter_mem
          sorry -- need to relate result_words to prime_words
        · sorry -- need to show prime property
      · cases' prime_words with head tail
        · intro word hw
          sorry -- need to show no prime length words
        · sorry -- need to handle recursive case