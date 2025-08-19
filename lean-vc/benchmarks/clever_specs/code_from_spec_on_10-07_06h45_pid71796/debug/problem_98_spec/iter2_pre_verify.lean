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
lemma countUppercaseVowels_empty : countUppercaseVowels "" = 0 := by
  simp [countUppercaseVowels]

-- LLM HELPER
lemma countUppercaseVowels_cons (c: Char) (s: String) :
  countUppercaseVowels (c.toString ++ s) = 
  (if c ∈ ['A', 'E', 'I', 'O', 'U'] then 1 else 0) + countUppercaseVowels s := by
  simp [countUppercaseVowels]
  rfl

-- LLM HELPER
lemma drop_two_toString (chars: List Char) :
  chars.length > 1 → (chars.drop 2).toString = (chars.drop 2).toString := by
  intro h
  rfl

-- LLM HELPER
lemma countUppercaseVowels_zero_iff (s: String) :
  countUppercaseVowels s = 0 ↔ ∀ i, i < s.toList.length → s.toList[i]! ∉ ['A', 'E', 'I', 'O', 'U'] := by
  constructor
  · intro h i hi
    by_contra hc
    have : countUppercaseVowels s > 0 := by
      simp [countUppercaseVowels]
      have : s.toList[i]! ∈ ['A', 'E', 'I', 'O', 'U'] := hc
      have : (s.toList.foldl (fun acc c => if c ∈ ['A', 'E', 'I', 'O', 'U'] then acc + 1 else acc) 0) > 0 := by
        rw [List.foldl_pos_iff]
        use i
        constructor
        · exact hi
        · simp [this]
      exact this
    rw [h] at this
    simp at this
  · intro h
    by_contra hc
    have : countUppercaseVowels s > 0 := by
      rw [Int.pos_iff_ne_zero]
      exact hc
    simp [countUppercaseVowels] at this
    have : ∃ i, i < s.toList.length ∧ s.toList[i]! ∈ ['A', 'E', 'I', 'O', 'U'] := by
      rw [List.foldl_pos_iff] at this
      exact this
    obtain ⟨i, hi, hc⟩ := this
    exact absurd hc (h i hi)

-- LLM HELPER
lemma countUppercaseVowels_recursive (s: String) :
  let chars := s.toList
  chars.length > 1 →
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
      have : chars = chars[0]! :: chars.tail := by
        rw [List.cons_head_tail]
        simp [List.length_pos_iff_ne_nil]
        intro h_empty
        rw [h_empty] at h
        simp at h
      rw [this]
      simp [List.foldl_cons]
      rw [if_pos hc]
      ring
  · right
    constructor
    · intro eq
      exact hc
    · intro _
      simp [countUppercaseVowels]
      have : chars = chars[0]! :: chars.tail := by
        rw [List.cons_head_tail]
        simp [List.length_pos_iff_ne_nil]
        intro h_empty
        rw [h_empty] at h
        simp at h
      rw [this]
      simp [List.foldl_cons]
      rw [if_neg hc]
      ring

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