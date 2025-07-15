def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(string: String) :=
-- spec
let spec (result: String) :=
let chars_in_result := result.toList;
let chars_in_string := string.toList;
chars_in_result.length = string.length ∧
(∀ i, i < chars_in_result.length →
  let c := chars_in_result[i]!;
  let c' := chars_in_string[i]!;
  (c.isUpper → c'.isLower) ∧
  (c.isLower → c'.isUpper) ∧
  ((¬ c.isUpper ∧ ¬ c.isLower) → c = c')
);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
def swapCase (c : Char) : Char :=
if c.isUpper then c.toLower else if c.isLower then c.toUpper else c

def implementation (string: String) : String := 
String.mk (string.toList.map swapCase)

-- LLM HELPER
lemma swapCase_spec (c : Char) : 
  let c' := swapCase c
  (c'.isUpper → c.isLower) ∧ (c'.isLower → c.isUpper) ∧ ((¬ c'.isUpper ∧ ¬ c'.isLower) → c' = c) := by
  simp [swapCase]
  constructor
  · intro h
    by_cases h1 : c.isUpper
    · simp [h1] at h
    · by_cases h2 : c.isLower
      · simp [h1, h2] at h
        exact h
      · simp [h1, h2] at h
  constructor
  · intro h
    by_cases h1 : c.isUpper
    · simp [h1] at h
      exact Char.isLower_toLower h1
    · by_cases h2 : c.isLower
      · simp [h1, h2] at h
      · simp [h1, h2] at h
  · intro h
    by_cases h1 : c.isUpper
    · simp [h1]
      have : (c.toLower).isUpper = false := Char.not_isUpper_toLower
      simp [this] at h
    · by_cases h2 : c.isLower
      · simp [h1, h2]
        have : (c.toUpper).isLower = false := Char.not_isLower_toUpper
        simp [this] at h
      · simp [h1, h2]

-- LLM HELPER
lemma map_length {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]

-- LLM HELPER
lemma String_mk_toList_map (s : String) (f : Char → Char) :
  (String.mk (s.toList.map f)).toList = s.toList.map f := by
  simp [String.toList_mk]

-- LLM HELPER
lemma List_get_map {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < (l.map f).length) :
  (l.map f)[i]! = f (l[i]!) := by
  have h' : i < l.length := by
    rw [← map_length f l]
    exact h
  simp [List.getElem_map]

theorem correctness
(string: String)
: problem_spec implementation string := by
  simp [problem_spec, implementation]
  let result := String.mk (string.toList.map swapCase)
  use result
  constructor
  · rfl
  · simp [String_mk_toList_map]
    constructor
    · exact map_length swapCase string.toList
    · intro i hi
      rw [List_get_map]
      exact swapCase_spec (string.toList[i]!)
      exact hi