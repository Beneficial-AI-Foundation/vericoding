-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def improve_product_name (s c : String) : String := sorry

theorem improve_result_is_valid (s c : String) :
  let result := improve_product_name s c
  (result = s ∨ result = "---" ∨ result.length = s.length) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem improve_result_less_than_competitor (s c : String) :
  let result := improve_product_name s c
  (result ≠ "---" → result ≤ c) := sorry

theorem improve_result_less_than_original (s c : String) :
  let result := improve_product_name s c
  (result ≠ "---" → result ≤ s) := sorry

theorem improve_maintains_chars (s c : String) :
  let result := improve_product_name s c
  (result ≠ "---" ∧ result ≠ s → result.data = s.data) := sorry

theorem improve_all_same_returns_self (s : String) (h : ∀ c ∈ s.data, c = 'A') :
  improve_product_name s (s ++ "Z") = s := sorry
-- </vc-theorems>