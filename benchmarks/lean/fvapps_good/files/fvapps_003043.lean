-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greet (name : String) (owner : String) : String := sorry

theorem greet_returns_hello_prefix (name owner : String) : 
  let result := greet name owner
  result.startsWith "Hello " = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem greet_returns_hello_boss_when_name_matches_owner (name owner : String) :
  name = owner → greet name owner = "Hello boss" := sorry

theorem greet_returns_hello_guest_when_name_differs (name owner : String) :
  name ≠ owner → greet name owner = "Hello guest" := sorry
-- </vc-theorems>