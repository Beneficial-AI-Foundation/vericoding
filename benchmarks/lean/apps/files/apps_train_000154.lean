def isSubsequence (s₁ s₂ : String) : Bool :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def shortestCommonSupersequence (s₁ s₂ : String) : String :=
sorry

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

/-
info: 'cabac'
-/
-- #guard_msgs in
-- #eval shortest_common_supersequence "abac" "cab"

/-
info: 6
-/
-- #guard_msgs in
-- #eval len shortest_common_supersequence("abc", "def")

/-
info: 'aaaaa'
-/
-- #guard_msgs in
-- #eval shortest_common_supersequence "aaaaa" "aa"

-- Apps difficulty: interview
-- Assurance level: unguarded