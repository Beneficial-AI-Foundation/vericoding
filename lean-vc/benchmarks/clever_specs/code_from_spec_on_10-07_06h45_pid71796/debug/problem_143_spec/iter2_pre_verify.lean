def problem_spec
-- function signature
(impl: String → String)
-- inputs
(sentence: String) :=
-- spec
let spec (result: String) :=
let words := sentence.splitOn " ";
let result_words := result.splitOn " ";
  1 ≤ sentence.length → sentence.length ≤ 100 →
  sentence.all (fun x => Char.isAlpha x || x = ' ') →
  result_words.length ≤ words.length ∧
  (∀ word ∈ result_words, word ∈ words ∧ Nat.Prime word.length) ∧
  match result_words with
  | [] => ∀ word ∈ words, ¬(Nat.Prime word.length)
  | head :: tail => True
-- program termination
∃ result, impl sentence = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else
    let rec check (i : Nat) : Bool :=
      if i * i > n then true
      else if n % i = 0 then false
      else check (i + 1)
    check 2

-- LLM HELPER
def filter_prime_words (words : List String) : List String :=
  words.filter (fun word => isPrime word.length)

-- LLM HELPER
def process_sentence_helper (words : List String) : List String :=
  match words with
  | [] => []
  | head :: tail => 
    if isPrime head.length then
      head :: process_sentence_helper tail
    else
      process_sentence_helper tail

def implementation (sentence : String) : String := 
  let words := sentence.splitOn " "
  let prime_words := process_sentence_helper words
  String.intercalate " " prime_words

-- LLM HELPER
lemma isPrime_iff_Nat_Prime (n : Nat) : isPrime n = true ↔ Nat.Prime n := by
  sorry

-- LLM HELPER
lemma splitOn_intercalate_inverse (words : List String) : 
  (String.intercalate " " words).splitOn " " = words := by
  sorry

-- LLM HELPER
lemma filter_membership (l : List String) (word : String) :
  word ∈ l.filter (fun w => isPrime w.length) → word ∈ l ∧ Nat.Prime word.length := by
  sorry

-- LLM HELPER
lemma filter_length_bound (l : List String) :
  (l.filter (fun w => isPrime w.length)).length ≤ l.length := by
  sorry

-- LLM HELPER
lemma process_helper_equiv_filter (words : List String) :
  process_sentence_helper words = words.filter (fun word => isPrime word.length) := by
  induction words with
  | nil => simp [process_sentence_helper]
  | cons head tail ih =>
    simp [process_sentence_helper, List.filter]
    split_ifs with h
    · simp [h, ih]
    · simp [h, ih]

-- LLM HELPER
lemma empty_filter_implies_no_prime (words : List String) :
  words.filter (fun word => isPrime word.length) = [] → 
  ∀ word ∈ words, ¬(Nat.Prime word.length) := by
  sorry

theorem correctness
(sentence : String)
: problem_spec implementation sentence := by
  unfold problem_spec
  use implementation sentence
  constructor
  · rfl
  · unfold implementation
    intro h_len_ge h_len_le h_alpha
    let words := sentence.splitOn " "
    let prime_words := process_sentence_helper words
    let result := String.intercalate " " prime_words
    rw [process_helper_equiv_filter]
    constructor
    · exact filter_length_bound words
    constructor
    · intro word h_mem
      rw [splitOn_intercalate_inverse] at h_mem
      have h_filter := filter_membership words word h_mem
      constructor
      · exact h_filter.1
      · rw [← isPrime_iff_Nat_Prime]
        exact h_filter.2
    · simp [splitOn_intercalate_inverse]
      cases' h : words.filter (fun word => isPrime word.length) with
      | nil => 
        rw [process_helper_equiv_filter]
        rw [h]
        simp [String.intercalate]
        intro word h_mem
        have h_no_prime := empty_filter_implies_no_prime words h
        rw [← isPrime_iff_Nat_Prime] at h_no_prime
        exact h_no_prime word h_mem
      | cons head tail =>
        simp