-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def to_integer (s: String) : Option Int := sorry 

theorem decimal_string_property (n : Int) :
  to_integer (toString n) = some n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binary_string_property (n : Int) (h : n ≥ 0):
  let binary := "0b" ++ toString n
  to_integer binary = some n := sorry

theorem hex_string_property (n : Int) (h : n ≥ 0):
  let hex := "0x" ++ toString n
  to_integer hex = some n := sorry

theorem octal_string_property (n : Int) (h : n ≥ 0):
  let octal := "0o" ++ toString n 
  to_integer octal = some n := sorry

theorem invalid_string_property (s : String) :
  ¬s.startsWith "0b" →
  ¬s.startsWith "0o" →
  ¬s.startsWith "0x" →
  (∀ c : Char, c ∈ s.data → ¬c.isDigit) →
  to_integer s = none := sorry

theorem edge_cases :
  to_integer "" = none ∧ 
  to_integer "+-123" = none ∧
  to_integer "0b" = none ∧
  to_integer "0x" = none ∧ 
  to_integer "0o" = none := sorry
-- </vc-theorems>