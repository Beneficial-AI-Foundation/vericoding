/-
### Count the number of Duplicates

Write a function that will return the count of **distinct case-insensitive** alphabetic characters and numeric digits that occur more than 
once in the input string. 
The input string can be assumed to contain only alphabets (both uppercase and lowercase) and numeric digits.

### Example
"abcde" -> 0             `# no characters repeats more than once`  
"aabbcde" -> 2           `# 'a' and 'b'`  
"aabBcde" -> 2           ``# 'a' occurs twice and 'b' twice (`b` and `B`)``  
"indivisibility" -> 1    `# 'i' occurs six times`  
"Indivisibilities" -> 2  `# 'i' occurs seven times and 's' occurs twice`  
"aA11" -> 2              `# 'a' and '1'`  
"ABBA" -> 2              `# 'A' and 'B' each occur twice`
-/

-- <vc-helpers>
-- </vc-helpers>

def duplicateCount (text : String) : Nat :=
  sorry

theorem duplicateCount_nonnegative (text : String) : 
  duplicateCount text ≥ 0 := by
  sorry

theorem duplicateCount_less_than_half_length (text : String) : 
  duplicateCount text ≤ text.length / 2 := by
  sorry

theorem duplicateCount_empty_and_unique (text : String) :
  -- Empty string has no duplicates
  duplicateCount "" = 0 ∧ 
  -- String with only unique chars has no duplicates
  (∀ s : String, (∀ c₁ c₂, c₁ ∈ s.data → c₂ ∈ s.data → c₁ = c₂) → duplicateCount s = 0) := by
  sorry

theorem duplicateCount_repeated_char (c : Char) :
  duplicateCount (String.mk [c, c]) = 1 := by
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval duplicate_count ""

/-
info: 0
-/
-- #guard_msgs in
-- #eval duplicate_count "abcde"

/-
info: 2
-/
-- #guard_msgs in
-- #eval duplicate_count "aabbcde"

/-
info: 2
-/
-- #guard_msgs in
-- #eval duplicate_count "aabBcde"

/-
info: 2
-/
-- #guard_msgs in
-- #eval duplicate_count "Indivisibilities"

-- Apps difficulty: introductory
-- Assurance level: guarded