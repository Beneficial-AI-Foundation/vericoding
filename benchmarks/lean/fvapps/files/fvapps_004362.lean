-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def replace_dashes_as_one (s : String) : String :=
sorry

def remove_dashes (s : String) : String :=
sorry

def containsSubstring (s : String) (sub : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_consecutive_dashes
  (s : String) :
  ¬ (containsSubstring (replace_dashes_as_one s) "--") ∧ 
  ¬ (containsSubstring (replace_dashes_as_one s) "- -") :=
sorry

theorem preserves_non_dash_chars
  (s : String) :
  remove_dashes s = remove_dashes (replace_dashes_as_one s) :=
sorry

theorem idempotent
  (s : String) :
  replace_dashes_as_one (replace_dashes_as_one s) = replace_dashes_as_one s :=
sorry

theorem dash_only_strings
  (s : String)
  (h : ∀ c, String.contains s c → (c = '-' ∨ c = ' ')) :
  (∀ c, String.contains (replace_dashes_as_one s) c → (c = '-' ∨ c = ' ')) ∧
  ¬ (containsSubstring (replace_dashes_as_one s) "--") ∧ 
  ¬ (containsSubstring (replace_dashes_as_one s) "- -") :=
sorry
-- </vc-theorems>