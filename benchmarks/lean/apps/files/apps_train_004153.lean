def NUMBER_WORDS : List String := ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]

def uncollapse (s : String) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def isSubstring (pattern : String) (s : String) : Bool :=
  sorry

theorem uncollapse_random_combinations (numbers : List String)
  (h : numbers ≠ [] ∧ ∀ n ∈ numbers, n ∈ NUMBER_WORDS) :
  uncollapse (String.join numbers) = String.join (List.intersperse " " numbers) :=
sorry

theorem uncollapse_preserves_order (numbers : List String)
  (h : numbers.length ≥ 2 ∧ ∀ n ∈ numbers, n ∈ NUMBER_WORDS) :
  (uncollapse (String.join numbers)).split (. == ' ') = numbers :=
sorry

theorem uncollapse_single_number (num : String)
  (h : num ∈ NUMBER_WORDS) :
  uncollapse num = num :=
sorry

theorem uncollapse_invalid_input (s : String)
  (h : ∀ word ∈ NUMBER_WORDS, isSubstring word s = false) :
  uncollapse s = "" :=
sorry

/-
info: 'three'
-/
-- #guard_msgs in
-- #eval uncollapse "three"

/-
info: 'eight six'
-/
-- #guard_msgs in
-- #eval uncollapse "eightsix"

/-
info: 'five four seven'
-/
-- #guard_msgs in
-- #eval uncollapse "fivefourseven"

-- Apps difficulty: introductory
-- Assurance level: unguarded