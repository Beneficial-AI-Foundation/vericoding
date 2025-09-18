-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greet (name : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem greet_special_case (name : String) :
  name = "Johnny" → greet name = "Hello, my love!" :=
  sorry

theorem greet_general_case (name : String) :
  name ≠ "Johnny" → greet name = "Hello, " ++ name ++ "!" :=
  sorry

theorem greet_starts_with_hello (name : String) :
  String.startsWith (greet name) "Hello" = true :=
  sorry

theorem greet_ends_with_exclamation (name : String) :
  String.endsWith (greet name) "!" = true :=
  sorry
-- </vc-theorems>