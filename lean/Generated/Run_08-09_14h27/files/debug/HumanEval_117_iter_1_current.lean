import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def is_consonant (c: Char) : Bool :=
  c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
  c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
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
lemma is_consonant_eq : ∀ c, is_consonant c = (c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha) := by
  intro c
  rfl

-- LLM HELPER  
lemma count_consonants_eq : ∀ word, count_consonants word = (word.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha)).length := by
  intro word
  simp [count_consonants, is_consonant_eq]

theorem correctness
(s: String)
(n: Nat)
: problem_spec implementation s n
:= by
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
          simp [count_consonants_eq] at h_result_empty
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
          simp [count_consonants_eq] at h_all
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
          · simp [count_consonants_eq] at h_first_count
            exact h_first_count
          · constructor
            · intro i h_i_lt
              by_contra h_contra
              simp [count_consonants_eq] at h_contra
              have h_filter_order := List.mem_filter.mpr ⟨List.get_mem _ i _, h_contra⟩
              have h_first_idx := List.idxOf_le_of_mem h_first_in
              have h_get_idx : List.idxOf (s.splitOn " ")[i]! (s.splitOn " ") ≤ i := List.idxOf_le_of_mem (List.get_mem _ i _)
              have : List.idxOf (s.splitOn " ")[i]! (s.splitOn " ") < List.idxOf first_word (s.splitOn " ") := by
                calc List.idxOf (s.splitOn " ")[i]! (s.splitOn " ")
                  ≤ i := h_get_idx
                  _ < List.idxOf first_word (s.splitOn " ") := h_i_lt
              have h_first_filter : first_word ∈ (s.splitOn " ").filter (fun word => count_consonants word = n) := by
                simp [List.mem_filter]
                constructor
                · exact h_first_in  
                · simp [count_consonants_eq]
                  exact h_first_count
              have h_get_filter : (s.splitOn " ")[i]! ∈ (s.splitOn " ").filter (fun word => count_consonants word = n) := by
                simp [List.mem_filter]
                constructor
                · exact List.get_mem _ i _
                · simp [count_consonants_eq]
                  exact h_contra
              have h_order := List.filter_preserves_order (s.splitOn " ") (fun word => count_consonants word = n)
              sorry
            · simp [List.tail_cons]
              sorry