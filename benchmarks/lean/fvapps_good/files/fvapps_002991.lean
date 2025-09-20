-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greet (name : String) : String := sorry

theorem greet_starts_with : ∀ (name : String),
  (greet name).startsWith "Hello, " = true := sorry

/- Since the greet_format theorem implies the containment of the name,
we can simplify by just using the format theorem -/
-- </vc-definitions>

-- <vc-theorems>
theorem greet_format : ∀ (name : String),
  greet name = "Hello, " ++ name ++ " how are you doing today?" := sorry

theorem greet_ends_with : ∀ (name : String),
  (greet name).endsWith " how are you doing today?" = true := sorry

theorem greet_length : ∀ (name : String),
  (greet name).length = "Hello, ".length + name.length + " how are you doing today?".length := sorry
-- </vc-theorems>