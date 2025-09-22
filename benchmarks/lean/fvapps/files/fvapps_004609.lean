-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hello (name: Option String := none) : String := sorry

def isSubstringOf (s₁ s₂ : String) : Prop := 
  ∃ a b, s₂ = a ++ s₁ ++ b
-- </vc-definitions>

-- <vc-theorems>
theorem hello_with_name_contains_capitalized {name: String} (h: name.length > 0):
  isSubstringOf (name.capitalize) (hello (some name)) := sorry

theorem hello_empty_is_world:
  hello none = "Hello, World!" := sorry

theorem hello_empty_string:
  hello (some "") = "Hello, World!" := sorry
-- </vc-theorems>