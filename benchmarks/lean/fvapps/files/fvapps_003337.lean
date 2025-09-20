-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>