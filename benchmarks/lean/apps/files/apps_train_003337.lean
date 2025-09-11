-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def parade_time (groups : List String) (location speed : Nat) (pref : String) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem parade_time_output_structure 
  (groups : List String) (location speed : Nat) (pref : String)
  (h1 : groups ≠ []) (h2 : ∀ g ∈ groups, g ≠ "") (h3 : speed > 0) (h4 : pref ≠ "") :
  let result := parade_time groups location speed pref
  ∀ x ∈ result, x ≥ 0 :=
sorry

theorem parade_time_length 
  (groups : List String) (location speed : Nat) (pref : String)
  (h1 : groups ≠ []) (h2 : ∀ g ∈ groups, g ≠ "") (h3 : speed > 0) (h4 : pref ≠ "") :
  let result := parade_time groups location speed pref
  List.length result = List.countP (· = pref) groups :=
sorry

theorem parade_time_no_matches
  (groups : List String) (location speed : Nat) (pref : String)
  (h1 : groups ≠ []) (h2 : ∀ g ∈ groups, g ≠ pref) (h3 : speed > 0) :
  parade_time groups location speed pref = [] :=
sorry

/-
info: [3]
-/
-- #guard_msgs in
-- #eval parade_time ["a", "b", "c", "d", "e", "f"] 3 2 "c"

/-
info: [2, 3]
-/
-- #guard_msgs in
-- #eval parade_time ["c", "b", "c", "d", "e", "f"] 3 2 "c"

/-
info: [10, 11, 13]
-/
-- #guard_msgs in
-- #eval parade_time ["a", "b", "c", "c", "e", "c"] 7 1 "c"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded