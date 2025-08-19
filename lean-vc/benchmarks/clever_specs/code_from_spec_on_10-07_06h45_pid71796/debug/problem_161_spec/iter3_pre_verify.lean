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
def swapCase (c : Char) : Char :=
  if c.isUpper then c.toLower
  else if c.isLower then c.toUpper
  else c

-- LLM HELPER
def processString (s : String) : String :=
  if s.all (λ c => not (c.isAlpha)) then
    String.mk s.toList.reverse
  else
    String.mk (s.toList.map swapCase)

def implementation (s: String) : String := processString s

-- LLM HELPER
lemma list_map_length {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [List.map_cons, List.length_cons, ih]

-- LLM HELPER
lemma string_mk_length (l : List Char) : (String.mk l).length = l.length := by
  simp [String.length_mk]

-- LLM HELPER
lemma string_toList_reverse_length (s : String) : s.toList.reverse.length = s.length := by
  simp [List.length_reverse, String.length_toList]

-- LLM HELPER
lemma string_get_mk (l : List Char) (i : Nat) (h : i < l.length) : (String.mk l).get! ⟨i⟩ = l.get ⟨i, h⟩ := by
  simp [String.get!_mk, String.get_mk]

-- LLM HELPER  
lemma swapCase_spec (c : Char) : 
  (c.isAlpha → ((c.isLower → c.toUpper = swapCase c) ∨ (c.isUpper → c.toLower = swapCase c))) ∧
  (¬ c.isAlpha → c = swapCase c) := by
  constructor
  · intro h_alpha
    unfold swapCase
    by_cases h_upper : c.isUpper
    · right
      intro h_upper'
      simp [h_upper]
    · left
      intro h_lower
      simp [h_upper]
      have : c.isLower := h_lower
      simp [this]
  · intro h_not_alpha
    unfold swapCase
    have h1 : ¬c.isUpper := by
      intro h_upper
      have : c.isAlpha := Char.isAlpha_of_isUpper h_upper
      contradiction
    have h2 : ¬c.isLower := by
      intro h_lower
      have : c.isAlpha := Char.isAlpha_of_isLower h_lower
      contradiction
    simp [h1, h2]

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec implementation processString
  let hasNoAlphabet := s.all (λ c => not (c.isAlpha))
  by_cases h : hasNoAlphabet
  · -- Case: no alphabetic characters
    use String.mk s.toList.reverse
    constructor
    · simp [h]
    · constructor
      · rw [string_mk_length, string_toList_reverse_length]
      · constructor
        · intro h_no_alpha
          simp [String.mk_toList]
        · intro h_has_alpha
          exfalso
          exact h_has_alpha h
  · -- Case: has alphabetic characters
    use String.mk (s.toList.map swapCase)
    constructor
    · simp [h]
    · constructor
      · rw [string_mk_length, list_map_length, String.length_toList]
      · constructor
        · intro h_no_alpha
          exfalso
          exact h h_no_alpha
        · intro h_has_alpha i hi
          have hi' : i < s.toList.length := by
            rw [String.length_toList] at hi
            exact hi
          let c := s.get! ⟨i⟩
          have h_get : c = s.toList.get ⟨i, hi'⟩ := by
            simp [String.get!_eq_get]
            rw [String.get_eq_getElem]
            simp
          have h_result_get : (String.mk (s.toList.map swapCase)).get! ⟨i⟩ = swapCase c := by
            rw [string_get_mk]
            simp [List.get_map, h_get]
          rw [h_result_get]
          exact swapCase_spec c