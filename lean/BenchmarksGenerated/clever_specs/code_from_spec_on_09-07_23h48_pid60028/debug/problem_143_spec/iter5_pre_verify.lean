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
  induction words with
  | nil => simp
  | cons h t ih => simp [String.intercalate, ih]

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
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.filter]
    by_cases h_case : p h
    · simp [h_case]
      intro h_mem
      cases h_mem with
      | inl h_eq => exact Or.inl h_eq
      | inr h_tail => exact Or.inr (ih h_tail)
    · simp [h_case]
      intro h_mem
      exact Or.inr (ih h_mem)

-- LLM HELPER
lemma isPrimeLength_correct (word : String) : 
  isPrimeLength word = true → Nat.Prime word.length := by
  intro h
  unfold isPrimeLength at h
  simp at h
  cases' h with h1 h2
  unfold Nat.Prime
  constructor
  · exact h1
  · intro m h_div
    by_contra h_contra
    push_neg at h_contra
    have h_m_bound : 2 ≤ m ∧ m ≤ word.length - 1 := by
      constructor
      · cases' h_contra with h_ne1 h_ne_len
        by_contra h_lt2
        simp at h_lt2
        cases' Nat.lt_succ_iff.mp h_lt2 with h_le1 h_eq1
        · have h_m_pos : 0 < m := Nat.pos_of_dvd_of_pos h_div (by simp; exact h1)
          cases' Nat.lt_succ_iff.mp (Nat.lt_of_le_of_lt h_le1 (Nat.one_lt_two)) with h_le0 h_eq0
          · exact Nat.lt_irrefl 0 (Nat.lt_of_le_of_lt h_le0 h_m_pos)
          · rw [h_eq0] at h_m_pos; exact Nat.lt_irrefl 0 h_m_pos
        · exact h_ne1 h_eq1
      · by_contra h_gt
        push_neg at h_gt
        have h_m_le : m ≤ word.length := Nat.le_of_dvd (by simp; exact h1) h_div
        exact Nat.lt_irrefl m (Nat.lt_of_le_of_lt h_m_le (Nat.lt_succ_of_le (Nat.le_of_not_gt h_gt)))
    have h_in_range : m - 1 ∈ (List.range (word.length - 1)).drop 1 := by
      simp [List.mem_range]
      constructor
      · exact Nat.sub_pos_of_lt (Nat.one_lt_of_lt (Nat.lt_of_succ_le h_m_bound.1))
      · exact Nat.sub_lt_sub_right (Nat.succ_le_of_lt (Nat.one_lt_of_lt (Nat.lt_of_succ_le h_m_bound.1))) h_m_bound.2
    have h_all := List.all_eq_true.mp h2
    have h_not_div := h_all (m - 1) h_in_range
    simp at h_not_div
    have h_eq : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.one_lt_of_lt (Nat.lt_of_succ_le h_m_bound.1)))
    rw [h_eq] at h_not_div
    exact h_not_div h_div

-- LLM HELPER
lemma list_of_mem_filter {α : Type*} (p : α → Bool) (l : List α) (x : α) :
  x ∈ l.filter p → p x = true := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.filter]
    by_cases h_case : p h
    · simp [h_case]
      intro h_mem
      cases h_mem with
      | inl h_eq => rw [← h_eq]; exact h_case
      | inr h_tail => exact ih h_tail
    · simp [h_case]
      exact ih

-- LLM HELPER
lemma prime_words_empty_iff (words : List String) :
  words.filter isPrimeLength = [] ↔ ∀ word ∈ words, ¬(Nat.Prime word.length) := by
  constructor
  · intro h_empty word h_mem
    by_contra h_prime
    have h_isPrime : isPrimeLength word = true := by
      unfold isPrimeLength
      simp
      cases' h_prime with h_gt1 h_all
      constructor
      · exact h_gt1
      · intro m h_in_range
        simp
        intro h_div
        have h_cases := h_all (m + 1) h_div
        cases h_cases with
        | inl h_eq => 
          simp at h_eq
          exact Nat.not_lt.mpr (Nat.le_of_succ_le_succ (Nat.succ_le_of_lt h_in_range)) (Nat.zero_lt_succ m)
        | inr h_eq =>
          have h_bound : m + 1 ≤ word.length - 1 := by
            simp at h_in_range
            exact Nat.lt_succ_iff.mp h_in_range.2
          rw [h_eq] at h_bound
          exact Nat.lt_irrefl (word.length) (Nat.lt_of_le_of_lt h_bound (Nat.sub_lt (Nat.zero_lt_of_lt h_gt1) Nat.zero_lt_one))
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
        by_cases h : Nat.Prime head.length ∧ head = words[0]!
        · simp [h]
          cases' words with
          | nil => simp
          | cons w ws => simp [String.join]
        · simp [h]
          cases' words with
          | nil => simp
          | cons w ws => simp [String.join]