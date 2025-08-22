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

def implementation (s: String) : Int := count_uppercase_vowels s.toList

-- LLM HELPER
lemma count_uppercase_vowels_correct (chars: List Char) :
  let uppercase_vowels := ['A', 'E', 'I', 'O', 'U']
  (count_uppercase_vowels chars = 0 ↔ ∀ i, i < chars.length → chars[i]! ∉ uppercase_vowels) ∧
  (1 < chars.length →
    (count_uppercase_vowels chars - 1 = count_uppercase_vowels (chars.drop 2) ↔ chars[0]! ∈ uppercase_vowels) ∨
    (count_uppercase_vowels chars = count_uppercase_vowels (chars.drop 2) ↔ chars[0]! ∉ uppercase_vowels)
  ) := by
  induction chars with
  | nil =>
    simp [count_uppercase_vowels]
    constructor
    · simp
    · simp
  | cons c rest ih =>
    simp [count_uppercase_vowels]
    split_ifs with h
    · simp [h]
      constructor
      · constructor
        · intro h_eq
          simp at h_eq
          have : count_uppercase_vowels rest ≥ 0 := by
            induction rest with
            | nil => simp [count_uppercase_vowels]
            | cons c' rest' ih' =>
              simp [count_uppercase_vowels]
              split_ifs <;> simp [ih']
          linarith
        · intro h_all
          have : c ∈ ['A', 'E', 'I', 'O', 'U'] := h
          have : c ∉ ['A', 'E', 'I', 'O', 'U'] := by
            apply h_all 0
            simp
          contradiction
      · intro h_len
        left
        constructor
        · intro h_eq
          simp at h_eq
          exact h
        · intro h_vowel
          rfl
    · simp [h]
      constructor
      · constructor
        · intro h_eq
          intro i h_i
          cases i with
          | zero => exact h
          | succ i' =>
            simp at h_i
            have ih_left := ih.left
            rw [ih_left.mpr] at h_eq
            apply h_eq
            simp
            exact Nat.lt_of_succ_lt_succ h_i
        · intro h_all
          have ih_left := ih.left
          rw [ih_left.mp]
          intro i h_i
          apply h_all
          simp
          exact Nat.succ_lt_succ h_i
      · intro h_len
        right
        constructor
        · intro h_eq
          exact h
        · intro h_not_vowel
          rfl

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  use count_uppercase_vowels s.toList
  constructor
  · rfl
  · exact count_uppercase_vowels_correct s.toList