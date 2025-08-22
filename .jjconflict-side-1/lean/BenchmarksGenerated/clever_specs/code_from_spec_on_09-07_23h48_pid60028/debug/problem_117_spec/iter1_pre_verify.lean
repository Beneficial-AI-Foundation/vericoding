def problem_spec
(implementation: String → Nat → List String)
(s: String)
(n: Nat) :=
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
    let first_word_idx := words.indexOf first_word
    (∀ i, i < first_word_idx →
      (words[i]!.data.filter (fun c => is_consonant c)).length ≠ n) ∧
    result.tail! =
      implementation ((words.drop (first_word_idx + 1)).foldl (fun acc word => acc ++ " " ++ word) "") n
  )
∃ result,
  implementation s n = result ∧
  spec result

-- LLM HELPER
def is_consonant (c: Char) : Bool :=
  c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
  c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
  c.isAlpha

-- LLM HELPER
def count_consonants (word: String) : Nat :=
  (word.data.filter (fun c => is_consonant c)).length

-- LLM HELPER
def find_first_word_with_n_consonants (words: List String) (n: Nat) : Option (String × Nat) :=
  match words with
  | [] => none
  | word :: rest =>
    if count_consonants word = n then
      some (word, 0)
    else
      match find_first_word_with_n_consonants rest n with
      | none => none
      | some (found_word, idx) => some (found_word, idx + 1)

-- LLM HELPER
def list_drop_until_after_index (words: List String) (idx: Nat) : List String :=
  words.drop (idx + 1)

-- LLM HELPER
def join_words (words: List String) : String :=
  match words with
  | [] => ""
  | [word] => word
  | word :: rest => word ++ " " ++ join_words rest

def implementation (s: String) (n: Nat) : List String :=
  if s.length = 0 then
    []
  else
    let words := s.splitOn " "
    match find_first_word_with_n_consonants words n with
    | none => []
    | some (first_word, idx) =>
      let remaining_words := list_drop_until_after_index words idx
      let remaining_string := join_words remaining_words
      first_word :: implementation remaining_string n

-- LLM HELPER
lemma is_consonant_eq (c: Char) : is_consonant c = (c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha) := by
  rfl

-- LLM HELPER
lemma count_consonants_eq (word: String) : count_consonants word = (word.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha)).length := by
  simp [count_consonants, is_consonant]

-- LLM HELPER
lemma find_first_word_some_iff (words: List String) (n: Nat) :
  (∃ word idx, find_first_word_with_n_consonants words n = some (word, idx)) ↔
  (∃ word, word ∈ words ∧ count_consonants word = n) := by
  sorry

-- LLM HELPER
lemma find_first_word_none_iff (words: List String) (n: Nat) :
  find_first_word_with_n_consonants words n = none ↔
  words.all (fun word => count_consonants word ≠ n) := by
  sorry

-- LLM HELPER
lemma join_words_foldl (words: List String) :
  join_words words = words.foldl (fun acc word => if acc = "" then word else acc ++ " " ++ word) "" := by
  sorry

theorem correctness
(s: String)
(n: Nat)
: problem_spec implementation s n := by
  simp [problem_spec]
  use implementation s n
  constructor
  · rfl
  · intro h_valid
    simp [implementation]
    split_ifs with h_empty
    · simp [h_empty]
      left
      exact h_empty
    · simp [h_empty]
      let words := s.splitOn " "
      cases h_find : find_first_word_with_n_consonants words n with
      | none =>
        simp
        right
        rw [find_first_word_none_iff] at h_find
        rw [count_consonants_eq] at h_find
        exact h_find
      | some pair =>
        obtain ⟨first_word, idx⟩ := pair
        simp
        constructor
        · simp [List.length_cons]
        · intro h_pos
          simp [List.get_cons_zero, List.tail_cons]
          sorry