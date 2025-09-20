-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def caffeineBuzz (n : Int) : String := sorry

theorem caffeineBuzz_returns_valid_string (n : Int) : 
  caffeineBuzz n = "CoffeeScript" ∨ 
  caffeineBuzz n = "JavaScript" ∨ 
  caffeineBuzz n = "Java" ∨ 
  caffeineBuzz n = "mocha_missing!" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem caffeineBuzz_divisibility_rules (n : Int) :
  (n % 12 = 0 → caffeineBuzz n = "CoffeeScript") ∧
  (n % 6 = 0 ∧ n % 12 ≠ 0 → caffeineBuzz n = "JavaScript") ∧
  (n % 3 = 0 ∧ n % 6 ≠ 0 → caffeineBuzz n = "Java") ∧ 
  (n % 3 ≠ 0 → caffeineBuzz n = "mocha_missing!") := sorry

theorem caffeineBuzz_hierarchical_rules (n : Int) :
  (caffeineBuzz n = "CoffeeScript" → n % 12 = 0) ∧
  (caffeineBuzz n = "JavaScript" → n % 6 = 0 ∧ n % 12 ≠ 0) ∧
  (caffeineBuzz n = "Java" → n % 3 = 0 ∧ n % 6 ≠ 0) ∧
  (caffeineBuzz n = "mocha_missing!" → n % 3 ≠ 0) := sorry
-- </vc-theorems>