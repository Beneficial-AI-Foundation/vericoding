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
def process_sentence_helper (words : List String) : List String :=
  match words with
  | [] => []
  | head :: tail => 
    if Nat.Prime head.length then
      head :: process_sentence_helper tail
    else
      process_sentence_helper tail

def implementation (sentence : String) : String := 
  let words := sentence.splitOn
  let prime_words := process_sentence_helper words
  String.join prime_words

-- LLM HELPER
lemma splitOn_join_inverse (words : List String) : 
  (String.join words).splitOn = words := by
  sorry

-- LLM HELPER
lemma filter_membership (l : List String) (word : String) :
  word ∈ l.filter (fun w => Nat.Prime w.length) → word ∈ l ∧ Nat.Prime word.length := by
  sorry

-- LLM HELPER
lemma filter_length_bound (l : List String) :
  (l.filter (fun w => Nat.Prime w.length)).length ≤ l.length := by
  sorry

-- LLM HELPER
lemma process_helper_equiv_filter (words : List String) :
  process_sentence_helper words = words.filter (fun word => Nat.Prime word.length) := by
  induction words with
  | nil => simp [process_sentence_helper]
  | cons head tail ih =>
    simp [process_sentence_helper, List.filter]
    split_ifs with h
    · simp [h, ih]
    · simp [h, ih]

-- LLM HELPER
lemma empty_filter_implies_no_prime (words : List String) :
  words.filter (fun word => Nat.Prime word.length) = [] → 
  ∀ word ∈ words, ¬(Nat.Prime word.length) := by
  sorry

-- LLM HELPER
lemma join_drop_splitOn (sentence : String) (n : Nat) :
  String.join (sentence.splitOn.drop n) = String.join (sentence.splitOn.drop n) := by
  rfl

theorem correctness
(sentence : String)
: problem_spec implementation sentence := by
  unfold problem_spec
  use implementation sentence
  constructor
  · rfl
  · unfold implementation
    intro h_len_ge h_len_le h_alpha
    let words := sentence.splitOn
    let prime_words := process_sentence_helper words
    let result := String.join prime_words
    rw [process_helper_equiv_filter]
    constructor
    · exact filter_length_bound words
    constructor
    · intro word h_mem
      rw [splitOn_join_inverse] at h_mem
      exact filter_membership words word h_mem
    · simp [splitOn_join_inverse]
      cases' h : words.filter (fun word => Nat.Prime word.length) with
      | nil => 
        rw [process_helper_equiv_filter]
        rw [h]
        simp [String.join]
        exact empty_filter_implies_no_prime words h
      | cons head tail =>
        rw [process_helper_equiv_filter]
        rw [h]
        simp [String.join]
        sorry