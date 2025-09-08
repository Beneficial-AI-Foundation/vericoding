import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def is_consonant (c: Char) : Bool :=
  !(['a', 'e', 'i', 'o', 'u'].contains c) && 
  !(['A', 'E', 'I', 'O', 'U'].contains c) && 
  c.isAlpha

-- LLM HELPER
def count_consonants (word: String) : Nat :=
  (word.data.filter is_consonant).length

def implementation (s: String) (n: Nat) : List String :=
  if s.isEmpty then
    []
  else
    let words := s.splitOn " "
    words.filter (fun word => count_consonants word = n)

def problem_spec
-- function signature
(implementation: String → Nat → List String)
-- inputs
(s: String)
(n: Nat) :=
-- spec
let spec (result : List String) :=
  let is_consonant (c: Char) :=
    c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
    c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
    c.isAlpha
  s.all (fun c => c = ' ' ∨ c.isAlpha) →
  let words := s.splitOn " "
  (result = [] ↔ (s.length = 0 ∨ words.all (fun word => (word.data.filter (fun c => is_consonant c)).length ≠ n))) ∧
  (result.length > 0 →
    let first_word := result[0]!
    first_word ∈ words ∧
    (first_word.data.filter (fun c => is_consonant c)).length = n ∧
    let first_word_idx := words.idxOf first_word
    (∀ i, i < first_word_idx →
      (words[i]!.data.filter (fun c => is_consonant c)).length ≠ n) ∧
    result.tail! =
      implementation ((words.drop (first_word_idx + 1)).foldl (fun acc word => acc ++ " " ++ word) "") n
  )

-- program termination
∃ result,
  implementation s n = result ∧
  spec result

-- LLM HELPER
lemma String.isEmpty_eq_length_zero (s : String) : s.isEmpty = (s.length = 0) := by
  simp only [String.isEmpty]
  rfl

-- LLM HELPER
lemma List.filter_nil_iff (p : α → Bool) (l : List α) : List.filter p l = [] ↔ ∀ x ∈ l, p x = false := by
  simp only [List.filter_eq_nil_iff, Bool.not_eq_true]

theorem correctness
(s: String)
(n: Nat)
: problem_spec implementation s n := by
  simp only [problem_spec]
  use implementation s n
  constructor
  · rfl
  · intro h
    simp only [implementation]
    constructor
    · constructor
      · intro h_result_empty
        by_cases h_empty : s.isEmpty
        · left
          simp only [String.isEmpty] at h_empty
          rw [String.isEmpty_eq_length_zero] at h_empty
          exact h_empty
        · right
          simp only [h_empty, ite_false] at h_result_empty
          rw [List.filter_nil_iff] at h_result_empty
          intro word h_word_in
          specialize h_result_empty word h_word_in
          simp only [Bool.decide_eq_false] at h_result_empty
          have count_eq : count_consonants word = 
            (word.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha)).length := by
            simp only [count_consonants, is_consonant]
            congr 2
            ext c
            simp only [List.contains, List.elem, Bool.and_eq_true, Bool.not_eq_true']
            constructor
            · intro h
              simp only [Bool.not_eq_true'] at h
              exact h
            · intro h
              simp only [Bool.not_eq_true']
              exact h
          rw [← count_eq] at h_result_empty
          exact h_result_empty
      · intro h_or
        cases h_or with
        | inl h_empty =>
          rw [String.isEmpty_eq_length_zero] at h_empty
          simp only [h_empty, String.isEmpty]
        | inr h_all =>
          simp only [String.isEmpty]
          split_ifs with h_empty_cond
          · simp
          · rw [List.filter_nil_iff]
            intro word h_word_in
            specialize h_all word h_word_in
            have count_eq : count_consonants word = 
              (word.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha)).length := by
              simp only [count_consonants, is_consonant]
              congr 2
              ext c
              simp only [List.contains, List.elem, Bool.and_eq_true, Bool.not_eq_true']
              constructor
              · intro h
                simp only [Bool.not_eq_true'] at h
                exact h
              · intro h
                simp only [Bool.not_eq_true']
                exact h
            rw [count_eq] at h_all
            simp only [Bool.decide_eq_false]
            exact h_all
    · intro h_result_nonempty
      simp only [String.isEmpty] at h_result_nonempty
      split_ifs at h_result_nonempty with h_empty
      · simp at h_result_nonempty
      · have h_filter_nonempty : (s.splitOn " ").filter (fun word => count_consonants word = n) ≠ [] := by
          simp only [List.length_pos_iff_ne_nil]
          exact h_result_nonempty
        have h_exists : ∃ first_word, first_word ∈ (s.splitOn " ").filter (fun word => count_consonants word = n) := by
          simp only [← List.length_pos_iff_ne_nil, List.length_pos_iff_exists_mem] at h_filter_nonempty
          exact h_filter_nonempty
        obtain ⟨first_word, h_first_in_filter⟩ := h_exists
        have h_first_in : first_word ∈ s.splitOn " " := by
          rw [List.mem_filter] at h_first_in_filter
          exact h_first_in_filter.1
        have h_first_count : count_consonants first_word = n := by
          rw [List.mem_filter] at h_first_in_filter
          simp only [Bool.decide_eq_true] at h_first_in_filter
          exact h_first_in_filter.2
        constructor
        · exact h_first_in
        · constructor
          · have count_eq : count_consonants first_word = 
              (first_word.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha)).length := by
              simp only [count_consonants, is_consonant]
              congr 2
              ext c
              simp only [List.contains, List.elem, Bool.and_eq_true, Bool.not_eq_true']
              constructor
              · intro h
                simp only [Bool.not_eq_true'] at h
                exact h
              · intro h
                simp only [Bool.not_eq_true']
                exact h
            rw [count_eq] at h_first_count
            exact h_first_count
          · constructor
            · intro i h_i_lt
              have h_first_is_head : first_word = ((s.splitOn " ").filter (fun word => count_consonants word = n))[0]! := by
                have h_nonempty : ((s.splitOn " ").filter (fun word => count_consonants word = n)).length > 0 := h_result_nonempty
                have h_mem_head : ((s.splitOn " ").filter (fun word => count_consonants word = n))[0]! ∈ ((s.splitOn " ").filter (fun word => count_consonants word = n)) := by
                  apply List.get!_mem
                  simp only [List.length_pos_iff_ne_nil] at h_nonempty
                  exact h_nonempty
                simp only [List.mem_filter] at h_mem_head
                have h_count_head : count_consonants (((s.splitOn " ").filter (fun word => count_consonants word = n))[0]!) = n := by
                  simp only [Bool.decide_eq_true] at h_mem_head
                  exact h_mem_head.2
                sorry
              sorry
            · sorry