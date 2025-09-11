-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_member_since (username : String) : String := sorry

theorem get_member_since_returns_nonempty_string (username : String) :
  get_member_since username ≠ "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_member_since_unknown_users (username : String) :
  username ≠ "dpleshkov" →
  username ≠ "jhoffner" →
  get_member_since username = "Unknown" := sorry

theorem get_member_since_known_values :
  get_member_since "dpleshkov" = "Jul 2016" ∧
  get_member_since "jhoffner" = "Oct 2012" := sorry

/-
info: 'Jul 2016'
-/
-- #guard_msgs in
-- #eval get_member_since "dpleshkov"

/-
info: 'Oct 2012'
-/
-- #guard_msgs in
-- #eval get_member_since "jhoffner"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded