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
def countUppercaseVowels (s: String) : Int :=
  let chars := s.toList
  let uppercase_vowels := ['A', 'E', 'I', 'O', 'U']
  chars.foldl (fun acc c => if c ∈ uppercase_vowels then acc + 1 else acc) 0

def implementation (s: String) : Int := countUppercaseVowels s

-- LLM HELPER
lemma foldl_count_positive_exists (chars : List Char) (vowels : List Char) :
  chars.foldl (fun acc c => if c ∈ vowels then acc + 1 else acc) 0 > 0 →
  ∃ i, i < chars.length ∧ chars[i]! ∈ vowels := by
  intro h
  induction chars with
  | nil => simp at h
  | cons head tail ih =>
    simp [List.foldl_cons] at h
    by_cases h_head : head ∈ vowels
    · use 0
      simp [h_head]
    · simp [h_head] at h
      have : ∃ i, i < tail.length ∧ tail[i]! ∈ vowels := ih h
      obtain ⟨i, hi, hc⟩ := this
      use i + 1
      constructor
      · simp
        omega
      · simp [List.get_cons_succ]
        exact hc

-- LLM HELPER
lemma foldl_count_zero_iff (chars : List Char) (vowels : List Char) :
  chars.foldl (fun acc c => if c ∈ vowels then acc + 1 else acc) 0 = 0 ↔
  ∀ i, i < chars.length → chars[i]! ∉ vowels := by
  constructor
  · intro h i hi
    by_contra hc
    have pos : chars.foldl (fun acc c => if c ∈ vowels then acc + 1 else acc) 0 > 0 := by
      induction chars with
      | nil => simp at hi
      | cons head tail ih =>
        simp [List.foldl_cons]
        by_cases h_head : head ∈ vowels
        · simp [h_head]
          omega
        · simp [h_head]
          by_cases i_zero : i = 0
          · simp [i_zero] at hc
            exact absurd hc h_head
          · have : i > 0 := Nat.pos_of_ne_zero i_zero
            have : i - 1 < tail.length := by
              simp at hi
              omega
            have : tail[i - 1]! ∈ vowels := by
              have : head :: tail = chars := rfl
              have : chars[i]! = tail[i - 1]! := by
                simp [List.get_cons_succ]
                congr
                omega
              rw [← this]
              exact hc
            exact ih this (by omega)
    rw [h] at pos
    simp at pos
  · intro h
    by_contra hc
    have pos : chars.foldl (fun acc c => if c ∈ vowels then acc + 1 else acc) 0 > 0 := by
      omega
    have : ∃ i, i < chars.length ∧ chars[i]! ∈ vowels := foldl_count_positive_exists chars vowels pos
    obtain ⟨i, hi, hc⟩ := this
    exact absurd hc (h i hi)

-- LLM HELPER
lemma countUppercaseVowels_zero_iff (s: String) :
  countUppercaseVowels s = 0 ↔ ∀ i, i < s.toList.length → s.toList[i]! ∉ ['A', 'E', 'I', 'O', 'U'] := by
  simp [countUppercaseVowels]
  exact foldl_count_zero_iff s.toList ['A', 'E', 'I', 'O', 'U']

-- LLM HELPER
lemma countUppercaseVowels_recursive (s: String) :
  let chars := s.toList
  1 < chars.length →
  (countUppercaseVowels s - 1 = countUppercaseVowels (chars.drop 2).toString ↔ chars[0]! ∈ ['A', 'E', 'I', 'O', 'U']) ∨
  (countUppercaseVowels s = countUppercaseVowels (chars.drop 2).toString ↔ chars[0]! ∉ ['A', 'E', 'I', 'O', 'U']) := by
  intro h
  by_cases hc : chars[0]! ∈ ['A', 'E', 'I', 'O', 'U']
  · left
    constructor
    · intro eq
      exact hc
    · intro _
      simp [countUppercaseVowels]
      have chars_nonempty : chars ≠ [] := by
        intro h_empty
        rw [h_empty] at h
        simp at h
      have : chars = chars[0]! :: chars.tail := by
        exact List.cons_head_tail chars_nonempty
      rw [this]
      simp [List.foldl_cons]
      rw [if_pos hc]
      have : chars.tail = chars.drop 1 := by
        rw [List.tail_drop]
      rw [this]
      have : (chars.drop 1).drop 1 = chars.drop 2 := by
        rw [List.drop_drop]
        simp
      rw [← this]
      rw [← List.drop_drop]
      simp [countUppercaseVowels]
      ring
  · right
    constructor
    · intro eq
      exact hc
    · intro _
      simp [countUppercaseVowels]
      have chars_nonempty : chars ≠ [] := by
        intro h_empty
        rw [h_empty] at h
        simp at h
      have : chars = chars[0]! :: chars.tail := by
        exact List.cons_head_tail chars_nonempty
      rw [this]
      simp [List.foldl_cons]
      rw [if_neg hc]
      have : chars.tail = chars.drop 1 := by
        rw [List.tail_drop]
      rw [this]
      have : (chars.drop 1).drop 1 = chars.drop 2 := by
        rw [List.drop_drop]
        simp
      rw [← this]
      rw [← List.drop_drop]
      simp [countUppercaseVowels]

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  use countUppercaseVowels s
  constructor
  · rfl
  · constructor
    · exact countUppercaseVowels_zero_iff s
    · intro h
      exact countUppercaseVowels_recursive s h