-- <vc-preamble>
def replace_dashes_as_one (s : String) : String := sorry

def remove_dashes (s : String) : String := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def containsSubstring (s : String) (sub : String) : Bool := sorry

theorem no_consecutive_dashes 
  (s : String) : 
  ¬ (containsSubstring (replace_dashes_as_one s) "--") ∧ 
  ¬ (containsSubstring (replace_dashes_as_one s) "- -") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem preserves_non_dash_chars
  (s : String) :
  remove_dashes s = remove_dashes (replace_dashes_as_one s) := sorry

theorem idempotent
  (s : String) :
  replace_dashes_as_one (replace_dashes_as_one s) = replace_dashes_as_one s := sorry

theorem dash_only_strings
  (s : String)
  (h : ∀ c, String.contains s c → (c = '-' ∨ c = ' ')) :
  (∀ c, String.contains (replace_dashes_as_one s) c → (c = '-' ∨ c = ' ')) ∧
  ¬ (containsSubstring (replace_dashes_as_one s) "--") ∧
  ¬ (containsSubstring (replace_dashes_as_one s) "- -") := sorry

/-
info: 'we-are- code-warriors.-'
-/
-- #guard_msgs in
-- #eval replace_dashes_as_one "we-are- - - code----warriors.-"

/-
info: 'a-b-c'
-/
-- #guard_msgs in
-- #eval replace_dashes_as_one "a---b- - -c"

/-
info: 'a-'
-/
-- #guard_msgs in
-- #eval replace_dashes_as_one "a------"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded