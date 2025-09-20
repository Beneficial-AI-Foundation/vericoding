-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def case_sensitive (s : String) : Bool × List String := sorry

theorem case_sensitive_returns_valid_output (s : String) : 
  let res := case_sensitive s
  (res.1 = true ∨ res.1 = false) ∧
  (∀ x ∈ res.2, String.length x = 1) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem case_sensitive_lowercase_only (s : String) :
  (∀ c ∈ s.data, 'a' ≤ c ∧ c ≤ 'z') →
  case_sensitive s = (true, []) := sorry

theorem case_sensitive_uppercase_only (s : String) :
  s ≠ "" →
  (∀ c ∈ s.data, 'A' ≤ c ∧ c ≤ 'Z') →
  let res := case_sensitive s
  res.1 = false ∧ 
  (∀ c ∈ s.data, (c.toString) ∈ res.2) ∧
  (∀ x ∈ res.2, ∃ c ∈ s.data, x = c.toString) := sorry
-- </vc-theorems>