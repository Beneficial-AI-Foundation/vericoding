-- <vc-preamble>
def romanValues : List (Char × Nat) :=
  [('I', 1), ('V', 5), ('X', 10), ('L', 50), ('C', 100), ('D', 500), ('M', 1000)]
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution (n : Nat) : String :=
sorry

def isSubstring (s₁ s₂ : String) : Bool :=
sorry

def convertToNums (s : String) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem monotonically_decreasing_values (n : Nat) (h : 1 ≤ n ∧ n ≤ 3999) :
  let numericValues := convertToNums (solution n)
  ∀ i j, i < j → j < numericValues.length →
    (numericValues.get ⟨i, sorry⟩) ≥ (numericValues.get ⟨j, sorry⟩) :=
sorry

theorem valid_roman_chars (n : Nat) (h : 1 ≤ n ∧ n ≤ 3999) :
  ∀ c, String.contains (solution n) c → c ∈ ['M', 'D', 'C', 'L', 'X', 'V', 'I'] :=
sorry

theorem length_constraints (n : Nat) (h : 1 ≤ n ∧ n ≤ 3999) :
  (n ≤ 3 → (solution n).length ≤ 3) ∧
  (n ≤ 8 → (solution n).length ≤ 4) ∧
  (n ≤ 39 → (solution n).length ≤ 6) :=
sorry

theorem no_four_consecutive_chars (n : Nat) (h : 1 ≤ n ∧ n ≤ 3999) :
  ¬isSubstring "IIII" (solution n) ∧
  ¬isSubstring "XXXX" (solution n) ∧
  ¬isSubstring "CCCC" (solution n) ∧
  ¬isSubstring "MMMM" (solution n) :=
sorry

theorem valid_subtractive_pairs (n : Nat) (h : 1 ≤ n ∧ n ≤ 3999) :
  ¬isSubstring "IL" (solution n) ∧
  ¬isSubstring "IC" (solution n) ∧
  ¬isSubstring "ID" (solution n) ∧
  ¬isSubstring "IM" (solution n) ∧
  ¬isSubstring "XD" (solution n) ∧
  ¬isSubstring "XM" (solution n) :=
sorry
-- </vc-theorems>