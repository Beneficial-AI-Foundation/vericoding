-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def VALID_OPERATORS : List String := ["Golden Telecom", "MTS", "Life:)", "Kyivstar", "Beeline", "no info"]

def detect_operator (number : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem detect_operator_returns_valid : ∀ (n : String),
  n.length = 11 → 
  n.front = '8' →
  detect_operator n ∈ VALID_OPERATORS :=
sorry

theorem detect_operator_consistent : ∀ (n : String),
  n.length = 11 →
  n.front = '8' →
  detect_operator n = detect_operator n :=
sorry

theorem detect_operator_handles_any_input : ∀ (n : String),
  ∃ (result : String),
  result = detect_operator n ∧
  result ∈ VALID_OPERATORS :=
sorry

theorem detect_operator_substring : ∀ (n n_modified : String),
  n.length = 11 →
  n.front = '8' →
  n_modified.front = '8' →
  n_modified.length = 11 →
  (∀ i : Nat, i ≥ 1 ∧ i < 4 → n.data.get! i = n_modified.data.get! i) →
  (∀ i : Nat, i ≥ 4 ∧ i < n_modified.length → n_modified.data.get! i = '0') →
  detect_operator n = detect_operator n_modified :=
sorry
-- </vc-theorems>