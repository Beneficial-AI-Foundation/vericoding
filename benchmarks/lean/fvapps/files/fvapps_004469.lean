-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greet (name : String) : String := sorry

theorem greet_starts_with_hello (name : String) (h : name.length > 0) :
  (greet name).startsWith "Hello " = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem greet_ends_with_exclamation (name : String) (h : name.length > 0) :
  (greet name).endsWith "!" = true := sorry

theorem greet_contains_capitalized_name (name : String) (h : name.length > 0) :
  ((greet name).drop "Hello ".length).dropRight 1 = name.capitalize := sorry
-- </vc-theorems>