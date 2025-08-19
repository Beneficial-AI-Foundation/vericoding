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
  let c := chars_in_result.get! i;
  let c' := chars_in_string.get! i;
  (c.isUpper → c'.isLower) ∧
  (c.isLower → c'.isUpper) ∧
  ((¬ c.isUpper ∧ ¬ c.isLower) → c = c')
);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
def swapCase (c : Char) : Char :=
  if c.isUpper then c.toLower
  else if c.isLower then c.toUpper
  else c

def implementation (string: String) : String := 
  String.mk (string.toList.map swapCase)

-- LLM HELPER
lemma swapCase_preserves_length (s : String) : 
  (String.mk (s.toList.map swapCase)).toList.length = s.length := by
  simp [String.toList_mk]

-- LLM HELPER
lemma swapCase_correct (c : Char) : 
  let c' := swapCase c
  (c'.isUpper → c.isLower) ∧
  (c'.isLower → c.isUpper) ∧
  ((¬ c'.isUpper ∧ ¬ c'.isLower) → c' = c) := by
  simp [swapCase]
  split_ifs with h1 h2
  · simp [Char.isUpper_toLower, h1]
  · simp [Char.isLower_toUpper, h2]
  · simp [h1, h2]

-- LLM HELPER
lemma list_get_map {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
  (l.map f).get! i = f (l.get! i) := by
  simp [List.get!_eq_get, List.get_map]

theorem correctness
(string: String)
: problem_spec implementation string := by
  simp [problem_spec, implementation]
  let result := String.mk (string.toList.map swapCase)
  use result
  constructor
  · rfl
  · simp [String.toList_mk]
    constructor
    · simp [List.length_map]
    · intro i hi
      rw [list_get_map]
      exact swapCase_correct (string.toList.get! i)