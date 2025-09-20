-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_minimal_parentheses (s: String) : String := sorry

def is_balanced (s: String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_balanced (s: String) : 
  let result := find_minimal_parentheses s
  is_balanced result ∧ ∀ c ∈ result.data, c = '(' ∨ c = ')' := sorry

theorem output_length_is_even (s: String) :
  let result := find_minimal_parentheses s
  result.length % 2 = 0 ∧ 
  (result.data.filter (· = '(')).length = (result.data.filter (· = ')')).length := sorry

theorem output_is_nested (s: String) :
  let result := find_minimal_parentheses s
  let n := result.length
  (∀ (i: Nat), i < n/2 → ∃ (p: String.Pos), result.get p = '(') ∧
  (∀ (i: Nat), n/2 ≤ i ∧ i < n → ∃ (p: String.Pos), result.get p = ')') := sorry
-- </vc-theorems>