def sortString (s : String) : String := sorry

def isAlpha (c : Char) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def isUpper (c : Char) : Bool := sorry
def isLower (c : Char) : Bool := sorry

theorem sort_string_preserves_length (s : String) :
  (sortString s).length = s.length := sorry

theorem sort_string_preserves_non_alpha (s : String) (i : String.Pos) :
  ¬(isAlpha (s.get i)) →
  (sortString s).get i = s.get i := sorry

theorem sort_string_sorts_alpha (s : String) :
  let result := sortString s
  let alphaChars := result.data.filter isAlpha
  ∀ i j, i < j → j < alphaChars.length →
    (alphaChars.get ⟨i, by sorry⟩).toLower ≤ (alphaChars.get ⟨j, by sorry⟩).toLower := sorry

theorem sort_string_preserves_case_counts (s : String) :
  let result := sortString s
  (result.data.filter isUpper).length = (s.data.filter isUpper).length ∧
  (result.data.filter isLower).length = (s.data.filter isLower).length := sorry

theorem sort_string_idempotent (s : String) :
  sortString (sortString s) = sortString s := sorry

/-
info: 'abc'
-/
-- #guard_msgs in
-- #eval sort_string "cba"

/-
info: 'abC'
-/
-- #guard_msgs in
-- #eval sort_string "Cba"

/-
info: 'a b c'
-/
-- #guard_msgs in
-- #eval sort_string "c b a"

-- Apps difficulty: introductory
-- Assurance level: unguarded