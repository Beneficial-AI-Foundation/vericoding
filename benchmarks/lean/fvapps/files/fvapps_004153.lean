-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def NUMBER_WORDS : List String := ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]

def uncollapse (s : String) : String :=
  sorry

def isSubstring (pattern : String) (s : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>