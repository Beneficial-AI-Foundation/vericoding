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
  word.length > 1 && (List.range (word.length - 1)).drop 1 |>.all (fun m => ¬(m + 1 ∣ word.length))

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
  sorry

-- LLM HELPER
lemma filter_mem {α : Type*} (p : α → Bool) (l : List α) (x : α) : 
  x ∈ l.filter p → x ∈ l := by
  sorry

-- LLM HELPER
lemma isPrimeLength_correct (word : String) : 
  isPrimeLength word = true → Nat.Prime word.length := by
  sorry

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
        have : word ∈ words.filter isPrimeLength := by rwa [← h_result_eq]
        exact List.of_mem_filter this
    
    · cases' prime_words with
      | nil => 
        simp [h_result_eq]
        intro word h_mem
        by_contra h_prime
        have : isPrimeLength word = true := by
          simp [isPrimeLength]
          constructor
          · exact Nat.lt_of_succ_lt h_prime.1
          · intro m h_div
            have : m = 1 ∨ m = word.length := h_prime.2 m h_div
            cases this with
            | inl h => simp [h]
            | inr h => simp [h, Nat.dvd_refl]
        have : word ∈ words.filter isPrimeLength := by
          simp [List.mem_filter]
          exact ⟨h_mem, this⟩
        have : prime_words ≠ [] := by
          simp [prime_words]
          exact List.ne_nil_of_mem this
        contradiction
      | cons head tail =>
        simp [h_result_eq]
        by_cases h : Nat.Prime head.length ∧ head = words[0]!
        · simp [h]
          cases' words with
          | nil => simp
          | cons w ws => simp [String.join]
        · simp [h]
          cases' words with
          | nil => simp
          | cons w ws => simp [String.join]