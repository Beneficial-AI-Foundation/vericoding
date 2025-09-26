-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rake_garden (garden : String) : String := sorry

-- Theorem 1: Result is space-separated words
-- </vc-definitions>

-- <vc-theorems>
theorem rake_garden_space_separated {garden : String} :
  let result := rake_garden garden
  let split := result.split (· = ' ')
  (String.intercalate " " split) = result := sorry

-- Theorem 2: All words in result are either 'rock' or 'gravel'

theorem rake_garden_valid_words {garden : String} : 
  let result := rake_garden garden
  let words := result.split (· = ' ')
  ∀ w ∈ words, w = "rock" ∨ w = "gravel" := sorry

-- Theorem 3: Rocks remain rocks, non-gravel becomes gravel

theorem rake_garden_transformations {garden : String} : 
  let original := garden.split (· = ' ')
  let result := (rake_garden garden).split (· = ' ')
  original.length = result.length ∧
  ∀ i, i < original.length →
    (original[i]! = "rock" → result[i]! = "rock") ∧
    (original[i]! ≠ "rock" ∧ original[i]! ≠ "gravel" → result[i]! = "gravel") := sorry

-- Theorem 4: Basic cases work as expected

theorem rake_garden_basic_cases :
  rake_garden "rock rock rock" = "rock rock rock" ∧ 
  rake_garden "gravel gravel" = "gravel gravel" ∧
  rake_garden "anything else" = "gravel gravel" := sorry
-- </vc-theorems>