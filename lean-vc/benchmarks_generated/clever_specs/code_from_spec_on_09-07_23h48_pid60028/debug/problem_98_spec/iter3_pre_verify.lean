def problem_spec
-- function signature
(implementation: String → Int)
-- inputs
(s: String) :=
-- spec
let uppercase_vowels := ['A', 'E', 'I', 'O', 'U']
let spec (result : Int) :=
  let chars := s.toList
  (result = 0 ↔ ∀ i, i < chars.length → chars[i]! ∉ uppercase_vowels) ∧
  (1 < chars.length →
    (result - 1 = implementation (chars.drop 2).toString ↔ chars[0]! ∈ uppercase_vowels) ∨
    (result = implementation (chars.drop 2).toString ↔ chars[0]! ∉ uppercase_vowels)
  )
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def count_uppercase_vowels (chars: List Char) : Int :=
  match chars with
  | [] => 0
  | c :: rest =>
    let count_rest := count_uppercase_vowels rest
    if c ∈ ['A', 'E', 'I', 'O', 'U'] then count_rest + 1 else count_rest

def implementation (s: String) : Int := count_uppercase_vowels s.data

-- LLM HELPER
lemma count_uppercase_vowels_zero (chars: List Char) :
  count_uppercase_vowels chars = 0 ↔ ∀ i, i < chars.length → chars[i]! ∉ ['A', 'E', 'I', 'O', 'U'] := by
  induction chars with
  | nil => simp [count_uppercase_vowels]
  | cons c rest ih =>
    simp [count_uppercase_vowels]
    split_ifs with h
    · simp [h]
      constructor
      · intro h_eq
        have : count_uppercase_vowels rest ≥ 0 := by
          induction rest with
          | nil => simp [count_uppercase_vowels]
          | cons c' rest' ih' =>
            simp [count_uppercase_vowels]
            split_ifs <;> omega
        omega
      · intro h_all
        have : c ∉ ['A', 'E', 'I', 'O', 'U'] := by
          apply h_all 0
          simp
        contradiction
    · simp [h]
      constructor
      · intro h_eq
        intro i h_i
        cases i with
        | zero => exact h
        | succ i' =>
          simp at h_i
          rw [ih] at h_eq
          apply h_eq
          simp
          exact Nat.lt_of_succ_lt_succ h_i
      · intro h_all
        rw [ih]
        intro i h_i
        apply h_all
        simp
        exact Nat.succ_lt_succ h_i

-- LLM HELPER
lemma count_uppercase_vowels_recursive (chars: List Char) :
  chars.length > 1 →
  ((count_uppercase_vowels chars - 1 = count_uppercase_vowels (chars.drop 2) ↔ chars[0]! ∈ ['A', 'E', 'I', 'O', 'U']) ∨
   (count_uppercase_vowels chars = count_uppercase_vowels (chars.drop 2) ↔ chars[0]! ∉ ['A', 'E', 'I', 'O', 'U'])) := by
  intro h_len
  cases chars with
  | nil => simp at h_len
  | cons c rest =>
    simp [count_uppercase_vowels]
    split_ifs with h
    · left
      constructor
      · intro h_eq
        exact h
      · intro h_vowel
        rfl
    · right
      constructor
      · intro h_eq
        exact h
      · intro h_not_vowel
        rfl

-- LLM HELPER
lemma string_data_toList_eq (s: String) : s.data = s.toList := by
  rfl

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  use count_uppercase_vowels s.data
  constructor
  · rfl
  · constructor
    · rw [string_data_toList_eq]
      exact count_uppercase_vowels_zero s.toList
    · intro h_len
      rw [string_data_toList_eq] at h_len
      have h_rec := count_uppercase_vowels_recursive s.toList h_len
      simp [implementation] at h_rec
      rw [string_data_toList_eq] at h_rec
      exact h_rec