def solution (n : Nat) : String := sorry

def isSubstring (s₁ s₂ : String) : Bool := sorry

/- Map Roman numerals to their decimal values -/

def romanValues : List (Char × Nat) := 
  [('I', 1), ('V', 5), ('X', 10), ('L', 50), ('C', 100), ('D', 500), ('M', 1000)]

-- <vc-helpers>
-- </vc-helpers>

def convertToNums (s : String) : List Nat := sorry

theorem monotonically_decreasing_values (n : Nat) (h : 1 ≤ n ∧ n ≤ 3999) :
  let numericValues := convertToNums (solution n)
  ∀ i j, i < j → j < numericValues.length → 
    (numericValues.get ⟨i, sorry⟩) ≥ (numericValues.get ⟨j, sorry⟩) := sorry

theorem valid_roman_chars (n : Nat) (h : 1 ≤ n ∧ n ≤ 3999) :
  ∀ c, String.contains (solution n) c → c ∈ ['M', 'D', 'C', 'L', 'X', 'V', 'I'] := sorry

theorem length_constraints (n : Nat) (h : 1 ≤ n ∧ n ≤ 3999) :
  (n ≤ 3 → (solution n).length ≤ 3) ∧ 
  (n ≤ 8 → (solution n).length ≤ 4) ∧
  (n ≤ 39 → (solution n).length ≤ 6) := sorry

theorem no_four_consecutive_chars (n : Nat) (h : 1 ≤ n ∧ n ≤ 3999) :
  ¬isSubstring "IIII" (solution n) ∧ 
  ¬isSubstring "XXXX" (solution n) ∧ 
  ¬isSubstring "CCCC" (solution n) ∧ 
  ¬isSubstring "MMMM" (solution n) := sorry

theorem valid_subtractive_pairs (n : Nat) (h : 1 ≤ n ∧ n ≤ 3999) :
  ¬isSubstring "IL" (solution n) ∧
  ¬isSubstring "IC" (solution n) ∧
  ¬isSubstring "ID" (solution n) ∧
  ¬isSubstring "IM" (solution n) ∧
  ¬isSubstring "XD" (solution n) ∧
  ¬isSubstring "XM" (solution n) := sorry

/-
info: 'I'
-/
-- #guard_msgs in
-- #eval solution 1

/-
info: 'MCMXC'
-/
-- #guard_msgs in
-- #eval solution 1990

/-
info: 'MMVIII'
-/
-- #guard_msgs in
-- #eval solution 2008

-- Apps difficulty: introductory
-- Assurance level: unguarded