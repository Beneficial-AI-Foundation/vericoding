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
    termination_by n + 1 - i
    decreasing_by
      simp_wf
      cases' Nat.lt_or_ge (i * i) n with h h
      · simp at h
        omega
      · simp at h
        omega
    check 2

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
  constructor
  · intro h
    sorry
  · intro h
    sorry

-- LLM HELPER
lemma splitOn_intercalate_inverse (words : List String) : 
  words ≠ [] → (String.intercalate " " words).splitOn " " = words := by
  sorry

-- LLM HELPER
lemma splitOn_intercalate_empty : 
  (String.intercalate " " []).splitOn " " = [""] := by
  sorry

-- LLM HELPER
lemma filter_membership (l : List String) (word : String) :
  word ∈ l.filter (fun w => isPrime w.length) → word ∈ l ∧ isPrime word.length = true := by
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

-- LLM HELPER
lemma process_helper_membership (words : List String) (word : String) :
  word ∈ process_sentence_helper words → word ∈ words ∧ Nat.Prime word.length := by
  rw [process_helper_equiv_filter]
  intro h
  have h_filter := filter_membership words word h
  constructor
  · exact h_filter.1
  · rw [← isPrime_iff_Nat_Prime]
    exact h_filter.2

-- LLM HELPER
lemma process_helper_length_bound (words : List String) :
  (process_sentence_helper words).length ≤ words.length := by
  rw [process_helper_equiv_filter]
  exact filter_length_bound words

-- LLM HELPER
lemma empty_string_splitOn : "".splitOn " " = [""] := by
  sorry

-- LLM HELPER
lemma splitOn_intercalate_result (words : List String) :
  let prime_words := process_sentence_helper words
  let result := String.intercalate " " prime_words
  (result.splitOn " " = prime_words ∨ (prime_words = [] ∧ result.splitOn " " = [""])) := by
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
    constructor
    · exact process_helper_length_bound words
    constructor
    · intro word h_mem
      have h_split := splitOn_intercalate_result words
      cases' h_split with h_case1 h_case2
      · rw [h_case1] at h_mem
        exact process_helper_membership words word h_mem
      · rw [h_case2.2] at h_mem
        simp at h_mem
        rw [h_mem]
        have h_empty := h_case2.1
        rw [process_helper_equiv_filter] at h_empty
        have h_no_prime := empty_filter_implies_no_prime words h_empty
        constructor
        · simp
        · simp [Nat.Prime]
    · cases' h : prime_words with
      | nil => 
        simp [String.intercalate, empty_string_splitOn]
        intro word h_mem
        rw [process_helper_equiv_filter] at h
        have h_no_prime := empty_filter_implies_no_prime words h
        exact h_no_prime word h_mem
      | cons head tail =>
        simp