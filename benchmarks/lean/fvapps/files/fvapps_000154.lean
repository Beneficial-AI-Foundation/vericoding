-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSubsequence (s₁ s₂ : String) : Bool :=
sorry

def shortestCommonSupersequence (s₁ s₂ : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem scs_contains_both_strings (s₁ s₂ : String) :
  let result := shortestCommonSupersequence s₁ s₂
  isSubsequence s₁ result = true ∧ isSubsequence s₂ result = true :=
sorry

theorem scs_same_string (s : String) :
  shortestCommonSupersequence s s = s :=
sorry

theorem scs_length_bounds (s₁ s₂ : String) :
  let result := shortestCommonSupersequence s₁ s₂
  result.length ≥ max s₁.length s₂.length ∧
  result.length ≤ s₁.length + s₂.length :=
sorry

theorem scs_empty_string (s : String) :
  shortestCommonSupersequence "" s = s ∧
  shortestCommonSupersequence s "" = s :=
sorry
-- </vc-theorems>