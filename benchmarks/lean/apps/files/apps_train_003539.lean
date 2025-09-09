-- <vc-helpers>
-- </vc-helpers>

def describeList (lst : List Int) : String :=
  sorry

theorem list_description_properties (lst : List Int) :
  describeList lst = match lst with
  | [] => "empty"
  | [_] => "singleton"
  | _ => "longer"
  :=
  sorry

theorem output_is_valid_string (lst : List Int) :
  describeList lst ∈ ["empty", "singleton", "longer"] :=
  sorry

/-
info: 'empty'
-/
-- #guard_msgs in
-- #eval describeList []

/-
info: 'singleton'
-/
-- #guard_msgs in
-- #eval describeList [1]

/-
info: 'longer'
-/
-- #guard_msgs in
-- #eval describeList [1, 2, 3]

-- Apps difficulty: introductory
-- Assurance level: unguarded