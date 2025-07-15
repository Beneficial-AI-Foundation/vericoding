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
def filter_prime_words (words : List String) : List String :=
  words.filter (fun word => Nat.Prime word.length)

-- LLM HELPER
def join_with_space (words : List String) : String :=
  String.intercalate " " words

def implementation (sentence : String) : String := 
  let words := sentence.splitOn
  let prime_words := filter_prime_words words
  join_with_space prime_words

-- LLM HELPER
lemma splitOn_join_inverse (words : List String) : 
  (String.intercalate " " words).splitOn = words := by
  sorry

-- LLM HELPER
lemma filter_subset {α : Type*} (p : α → Bool) (l : List α) : 
  (l.filter p).length ≤ l.length := by
  sorry

-- LLM HELPER
lemma filter_mem {α : Type*} (p : α → Bool) (l : List α) (x : α) : 
  x ∈ l.filter p → x ∈ l := by
  sorry

-- LLM HELPER
lemma filter_prop {α : Type*} (p : α → Bool) (l : List α) (x : α) : 
  x ∈ l.filter p → p x = true := by
  sorry

theorem correctness
(sentence : String)
: problem_spec implementation sentence := by
  unfold problem_spec implementation
  simp [filter_prime_words, join_with_space]
  use String.intercalate " " (sentence.splitOn.filter (fun word => Nat.Prime word.length))
  constructor
  · rfl
  · intro h1 h2 h3
    let words := sentence.splitOn
    let prime_words := words.filter (fun word => Nat.Prime word.length)
    let result_words := (String.intercalate " " prime_words).splitOn
    
    have h_result_eq : result_words = prime_words := by
      simp [splitOn_join_inverse]
    
    constructor
    · rw [h_result_eq]
      exact filter_subset (fun word => Nat.Prime word.length) words
    
    constructor
    · intro word h_mem
      rw [h_result_eq] at h_mem
      constructor
      · exact filter_mem (fun word => Nat.Prime word.length) words word h_mem
      · have := filter_prop (fun word => Nat.Prime word.length) words word h_mem
        simp at this
        exact this
    
    · cases' prime_words with
      | nil => 
        simp [h_result_eq]
        intro word h_mem
        by_contra h_prime
        have : word ∈ words.filter (fun word => Nat.Prime word.length) := by
          simp [h_prime, h_mem]
        rw [← List.filter_eq_nil_iff] at this
        sorry
      | cons head tail =>
        simp [h_result_eq]
        sorry