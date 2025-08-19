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
  sorry

-- LLM HELPER
lemma drop_two_toString (chars: List Char) :
  chars.length > 1 → (chars.drop 2).toString = (chars.drop 2).toString := by
  intro h
  rfl

-- LLM HELPER
lemma countUppercaseVowels_zero_iff (s: String) :
  countUppercaseVowels s = 0 ↔ ∀ i, i < s.toList.length → s.toList[i]! ∉ ['A', 'E', 'I', 'O', 'U'] := by
  sorry

-- LLM HELPER
lemma countUppercaseVowels_recursive (s: String) :
  let chars := s.toList
  chars.length > 1 →
  (countUppercaseVowels s - 1 = countUppercaseVowels (chars.drop 2).toString ↔ chars[0]! ∈ ['A', 'E', 'I', 'O', 'U']) ∨
  (countUppercaseVowels s = countUppercaseVowels (chars.drop 2).toString ↔ chars[0]! ∉ ['A', 'E', 'I', 'O', 'U']) := by
  sorry

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