-- <vc-helpers>
-- </vc-helpers>

def hello (name: Option String := none) : String := sorry

def isSubstringOf (s₁ s₂ : String) : Prop := 
  ∃ a b, s₂ = a ++ s₁ ++ b

theorem hello_with_name_contains_capitalized {name: String} (h: name.length > 0):
  isSubstringOf (name.capitalize) (hello (some name)) := sorry

theorem hello_empty_is_world:
  hello none = "Hello, World!" := sorry

theorem hello_empty_string:
  hello (some "") = "Hello, World!" := sorry

/-
info: 'Hello, World!'
-/
-- #guard_msgs in
-- #eval hello 

/-
info: 'Hello, World!'
-/
-- #guard_msgs in
-- #eval hello ""

/-
info: 'Hello, Alice!'
-/
-- #guard_msgs in
-- #eval hello "alice"

/-
info: 'Hello, John!'
-/
-- #guard_msgs in
-- #eval hello "jOHN"

-- Apps difficulty: introductory
-- Assurance level: unguarded