-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def travel (r : String) (zipcode : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem travel_empty_zipcode (addrs : String) :
  travel addrs "" = ":/" := by sorry

theorem travel_invalid_zipcode (addrs : String) (zip : String) :
  zip = "AB 123" →
  travel addrs zip = "AB 123:/" := by sorry

theorem travel_valid_zipcode_format (addrs : String) (stateZip : String) :
  addrs ≠ "" →
  let result := travel addrs stateZip
  result.startsWith s!"{stateZip}:" ∧
  result.contains '/' := by sorry

theorem travel_valid_result_components (addrs : String) (stateZip : String) 
    (result : String) (h : result = travel addrs stateZip) :
  result ≠ s!"{stateZip}:/" →
  let components := result.split (· == '/')
  let streets := ((components.get? 0).getD "").split (· == ':')
  let numbers := (components.get? 1).getD ""
  (∀ n ∈ (numbers.split (· == ',')), n.all Char.isDigit) ∧
  (∀ s ∈ ((streets.get? 1).getD "").split (· == ','), s.all (fun c => c.isAlpha ∨ c == ' ')) := by sorry

theorem travel_malformed_input (badInput : String) :
  let result := travel badInput "ST 12345"
  result = "ST 12345:/" ∨
  (result.startsWith "ST 12345:" ∧ result.contains '/') := by sorry

/-
info: 'OH 43071:Main Street St. Louisville,Main Long Road St. Louisville/123,432'
-/
-- #guard_msgs in
-- #eval travel "123 Main Street St. Louisville OH 43071,432 Main Long Road St. Louisville OH 43071,786 High Street Pollocksville NY 56432" "OH 43071"

/-
info: 'NY 56432:High Street Pollocksville/786'
-/
-- #guard_msgs in
-- #eval travel r "NY 56432"

/-
info: 'NY 5643:/'
-/
-- #guard_msgs in
-- #eval travel r "NY 5643"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded