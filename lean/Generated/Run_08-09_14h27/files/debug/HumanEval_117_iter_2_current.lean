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
lemma is_consonant_iff (c : Char) : 
  is_consonant c = true ↔ 
  c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha = true := by
  simp [is_consonant, List.contains]
  constructor
  · intro h
    simp at h
    exact h
  · intro h  
    simp
    exact h

-- LLM HELPER  
lemma count_consonants_eq (word : String) : 
  count_consonants word = 
  (word.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha)).length := by
  simp [count_consonants]
  congr
  ext c
  rw [← is_consonant_iff]
  simp [Bool.decide_eq_true]

theorem correctness
(s: String)
(n: Nat)
: problem_spec implementation s n := by
  simp [problem_spec]
  use implementation s n
  constructor
  · rfl
  · intro h
    simp [implementation]
    constructor
    · constructor
      · intro h_result_empty
        by_cases h_empty : s.isEmpty
        · left
          simp [String.isEmpty] at h_empty
          exact h_empty
        · right
          simp [h_empty] at h_result_empty
          simp [List.filter_eq_nil] at h_result_empty
          intro word h_word_in
          specialize h_result_empty word h_word_in
          rw [count_consonants_eq] at h_result_empty
          exact h_result_empty
      · intro h_or
        cases h_or with
        | inl h_empty =>
          simp [h_empty, String.isEmpty]
        | inr h_all =>
          simp [String.isEmpty]
          intro h_not_empty
          simp [List.filter_eq_nil]
          intro word h_word_in
          specialize h_all word h_word_in
          rw [← count_consonants_eq] at h_all
          exact h_all
    · intro h_result_nonempty
      simp [String.isEmpty] at h_result_nonempty
      by_cases h_empty : s = ""
      · simp [h_empty] at h_result_nonempty
      · simp [h_empty] at h_result_nonempty
        have h_filter_nonempty : (s.splitOn " ").filter (fun word => count_consonants word = n) ≠ [] := h_result_nonempty
        simp [List.filter_ne_nil] at h_filter_nonempty
        obtain ⟨first_word, h_first_in, h_first_count⟩ := h_filter_nonempty
        constructor
        · exact h_first_in
        · constructor
          · rw [count_consonants_eq] at h_first_count
            exact h_first_count
          · constructor
            · intro i h_i_lt
              by_contra h_contra
              rw [count_consonants_eq] at h_contra
              have h_mem_filter := List.mem_filter.mpr ⟨List.get_mem _ i _, h_first_count⟩
              have h_get_filter := List.mem_filter.mpr ⟨List.get_mem _ i _, h_contra⟩
              simp at h_mem_filter h_get_filter
              have h_filter := (s.splitOn " ").filter (fun word => count_consonants word = n)
              have h_get_in_filter : (s.splitOn " ")[i]! ∈ h_filter := by
                simp [h_filter, List.mem_filter]
                exact ⟨List.get_mem _ i _, by rwa [← count_consonants_eq]⟩
              have h_first_in_filter : first_word ∈ h_filter := by
                simp [h_filter, List.mem_filter]
                exact ⟨h_first_in, by rwa [← count_consonants_eq]⟩
              have h_first_head : h_filter.head? = some first_word := by
                have : h_filter ≠ [] := List.ne_nil_of_mem h_first_in_filter
                simp [List.head?_eq_some_iff]
                constructor
                · exact this
                · simp [h_filter]
                  apply List.get_of_mem
                  exact List.mem_filter.mpr ⟨h_first_in, by rwa [← count_consonants_eq]⟩
              simp
            · simp [List.tail_cons]
              rfl