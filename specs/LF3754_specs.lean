-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sortString (s : String) : String :=
sorry

def isAlpha (c : Char) : Bool :=
sorry

def isUpper (c : Char) : Bool :=
sorry

def isLower (c : Char) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_string_preserves_length (s : String) :
  (sortString s).length = s.length :=
sorry

theorem sort_string_preserves_non_alpha (s : String) (i : String.Pos) :
  ¬(isAlpha (s.get i)) →
  (sortString s).get i = s.get i :=
sorry

theorem sort_string_sorts_alpha (s : String) :
  let result := sortString s
  let alphaChars := result.data.filter isAlpha
  ∀ i j, i < j → j < alphaChars.length →
    (alphaChars.get ⟨i, by sorry⟩).toLower ≤ (alphaChars.get ⟨j, by sorry⟩).toLower :=
sorry

theorem sort_string_preserves_case_counts (s : String) :
  let result := sortString s
  (result.data.filter isUpper).length = (s.data.filter isUpper).length ∧
  (result.data.filter isLower).length = (s.data.filter isLower).length :=
sorry

theorem sort_string_idempotent (s : String) :
  sortString (sortString s) = sortString s :=
sorry
-- </vc-theorems>