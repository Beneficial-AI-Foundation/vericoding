def problem_spec
-- function signature
(impl: String → String)
-- inputs
(string : String) :=
-- spec
let spec (result: String) :=
result.length = string.length ∧
let hasNoAlphabet := string.all (λ c => not (c.isAlpha));
(hasNoAlphabet →
  result.toList = string.toList.reverse) ∧
(hasNoAlphabet = false →
  ∀ i, i < string.length →
  let c := string.get! ⟨i⟩;
  (c.isAlpha → ((c.isLower → c.toUpper = result.get! ⟨i⟩) ∨
              (c.isUpper → c.toLower = result.get! ⟨i⟩))) ∧
  (¬ c.isAlpha → c = result.get! ⟨i⟩))
-- program terminates
∃ result, impl string = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def toggleCase (c : Char) : Char :=
  if c.isLower then c.toUpper
  else if c.isUpper then c.toLower
  else c

def implementation (s: String) : String :=
  if s.all (λ c => not (c.isAlpha)) then
    String.mk s.toList.reverse
  else
    String.mk (s.toList.map toggleCase)

-- LLM HELPER
lemma string_mk_toList_reverse_length (s : String) :
  (String.mk s.toList.reverse).length = s.length := by
  simp [String.length]

-- LLM HELPER
lemma string_mk_map_length (s : String) (f : Char → Char) :
  (String.mk (s.toList.map f)).length = s.length := by
  simp [String.length]

-- LLM HELPER
lemma string_mk_toList_reverse_toList (s : String) :
  (String.mk s.toList.reverse).toList = s.toList.reverse := by
  simp

-- LLM HELPER
lemma string_mk_map_get (s : String) (f : Char → Char) (i : Fin s.length) :
  (String.mk (s.toList.map f)).get! ⟨i.val⟩ = f (s.get! ⟨i.val⟩) := by
  simp [String.get!, String.mk]
  have h : i.val < s.toList.length := by simp [String.length] at i; exact i.isLt
  rw [List.get_map _ _ h]
  congr

-- LLM HELPER
lemma toggleCase_preserves_alpha (c : Char) :
  c.isAlpha → (c.isLower → c.toUpper = toggleCase c) ∨ (c.isUpper → c.toLower = toggleCase c) := by
  intro h
  unfold toggleCase
  cases' Char.isLower c with h1 h2
  · left
    intro h_lower
    simp [h1]
  · right
    intro h_upper
    simp [h1]

-- LLM HELPER
lemma toggleCase_preserves_non_alpha (c : Char) :
  ¬c.isAlpha → c = toggleCase c := by
  intro h
  unfold toggleCase
  simp [Char.isLower_iff_isAlpha, Char.isUpper_iff_isAlpha, h]

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec implementation
  simp only [exists_prop]
  let hasNoAlphabet := s.all (λ c => not (c.isAlpha))
  split_ifs with h
  · -- Case: hasNoAlphabet = true
    use String.mk s.toList.reverse
    constructor
    · rfl
    · constructor
      · exact string_mk_toList_reverse_length s
      · constructor
        · intro h_no_alpha
          exact string_mk_toList_reverse_toList s
        · intro h_has_alpha
          exfalso
          exact h_has_alpha h
  · -- Case: hasNoAlphabet = false
    use String.mk (s.toList.map toggleCase)
    constructor
    · rfl
    · constructor
      · exact string_mk_map_length s toggleCase
      · constructor
        · intro h_no_alpha
          exfalso
          exact h h_no_alpha
        · intro h_has_alpha
          intro i hi
          constructor
          · intro h_alpha
            have h_get : (String.mk (s.toList.map toggleCase)).get! ⟨i⟩ = toggleCase (s.get! ⟨i⟩) := by
              rw [string_mk_map_get]
              simp [hi]
            rw [h_get]
            exact toggleCase_preserves_alpha (s.get! ⟨i⟩) h_alpha
          · intro h_not_alpha
            have h_get : (String.mk (s.toList.map toggleCase)).get! ⟨i⟩ = toggleCase (s.get! ⟨i⟩) := by
              rw [string_mk_map_get]
              simp [hi]
            rw [h_get]
            exact toggleCase_preserves_non_alpha (s.get! ⟨i⟩) h_not_alpha