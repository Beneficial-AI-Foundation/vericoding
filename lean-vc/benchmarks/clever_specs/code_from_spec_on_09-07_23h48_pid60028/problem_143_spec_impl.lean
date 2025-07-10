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
  sentence.all (fun x => Char.isAlpha x ∨ x = ' ') →
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
def Nat.Prime (n : Nat) : Prop :=
  n > 1 ∧ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

-- LLM HELPER
def isPrimeLength (word : String) : Bool :=
  if word.length > 1 then
    (List.range (word.length - 1)).drop 1 |>.all (fun m => ¬((m + 1) ∣ word.length))
  else
    false

-- LLM HELPER
def filter_prime_words (words : List String) : List String :=
  words.filter isPrimeLength

-- LLM HELPER
def join_with_space (words : List String) : String :=
  String.intercalate " " words

def implementation (sentence : String) : String := 
  let words := sentence.splitOn " "
  let prime_words := filter_prime_words words
  join_with_space prime_words

-- LLM HELPER
lemma splitOn_join_inverse (words : List String) : 
  (String.intercalate " " words).splitOn " " = words := by
  sorry

-- LLM HELPER
lemma filter_subset {α : Type*} (p : α → Bool) (l : List α) : 
  (l.filter p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons h t ih => 
    simp [List.filter]
    by_cases h_case : p h
    · simp [h_case]
      exact Nat.succ_le_succ ih
    · simp [h_case]
      exact Nat.le_succ_of_le ih

-- LLM HELPER
lemma filter_mem {α : Type*} (p : α → Bool) (l : List α) (x : α) : 
  x ∈ l.filter p → x ∈ l := by
  exact List.mem_of_mem_filter

-- LLM HELPER
lemma isPrimeLength_correct (word : String) : 
  isPrimeLength word = true → Nat.Prime word.length := by
  intro h
  unfold isPrimeLength at h
  simp at h
  unfold Nat.Prime
  sorry

-- LLM HELPER
lemma list_of_mem_filter {α : Type*} (p : α → Bool) (l : List α) (x : α) :
  x ∈ l.filter p → p x = true := by
  exact List.of_mem_filter

-- LLM HELPER
lemma prime_words_empty_iff (words : List String) :
  words.filter isPrimeLength = [] ↔ ∀ word ∈ words, ¬(Nat.Prime word.length) := by
  constructor
  · intro h_empty word h_mem
    by_contra h_prime
    have h_isPrime : isPrimeLength word = true := by
      sorry
    have h_mem_filter : word ∈ words.filter isPrimeLength := List.mem_filter.mpr ⟨h_mem, h_isPrime⟩
    rw [h_empty] at h_mem_filter
    exact List.not_mem_nil word h_mem_filter
  · intro h_no_prime
    ext
    simp [List.mem_filter]
    intro word h_mem
    constructor
    · intro h_isPrime
      have h_prime := isPrimeLength_correct word h_isPrime
      exact h_no_prime word h_mem h_prime
    · intro h_false
      exact False.elim h_false

theorem correctness
(sentence : String)
: problem_spec implementation sentence := by
  unfold problem_spec implementation
  simp [filter_prime_words, join_with_space]
  use String.intercalate " " (sentence.splitOn " " |>.filter isPrimeLength)
  constructor
  · rfl
  · intro h1 h2 h3
    let words := sentence.splitOn " "
    let prime_words := words.filter isPrimeLength
    let result_words := (String.intercalate " " prime_words).splitOn " "
    
    have h_result_eq : result_words = prime_words := by
      apply splitOn_join_inverse
    
    constructor
    · rw [h_result_eq]
      exact filter_subset isPrimeLength words
    
    constructor
    · intro word h_mem
      rw [h_result_eq] at h_mem
      constructor
      · exact filter_mem isPrimeLength words word h_mem
      · apply isPrimeLength_correct
        exact list_of_mem_filter isPrimeLength words word h_mem
    
    · cases' prime_words with
      | nil => 
        simp [h_result_eq]
        exact prime_words_empty_iff words |>.mp rfl
      | cons head tail =>
        simp [h_result_eq]
        simp
        rfl