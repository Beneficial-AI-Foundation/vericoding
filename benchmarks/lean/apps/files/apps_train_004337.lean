def debug (s : String) : String := sorry

def String.containsSubstr (s str : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def String.countOccurrences (s str : String) : Nat := sorry

theorem debug_basic_properties (s : String) : 
  let result := debug s
  (¬ result.containsSubstr "bug" ∨ result.containsSubstr "bugs") ∧ 
  result.length ≤ s.length ∧
  result = s.replace "bug" "" :=
sorry

theorem debug_preserves_bugs (s : String) (h : ∀ c ∈ s.data, c = 'b' ∨ c = 'u' ∨ c = 'g' ∨ c = 's') :
  (debug s).countOccurrences "bugs" = s.countOccurrences "bugs" :=
sorry

theorem debug_idempotent (s : String) :
  debug (debug s) = debug s :=
sorry

/-
info: 'ooobuoobugsoo'
-/
-- #guard_msgs in
-- #eval debug "obugobugobuoobugsoo"

/-
info: 'bugs gy'
-/
-- #guard_msgs in
-- #eval debug "bugs buggy"

/-
info: ''
-/
-- #guard_msgs in
-- #eval debug "bugbugbugbug"

-- Apps difficulty: introductory
-- Assurance level: unguarded