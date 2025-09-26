-- <vc-preamble>
def get_oddity (n : Int) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def oddest (nums : List Int) : Option Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem oddest_empty (nums : List Int) :
  nums = [] → oddest nums = none :=
  sorry

theorem oddest_in_list {nums : List Int} {result : Int} :
  oddest nums = some result → result ∈ nums :=
  sorry

theorem oddest_null_tie_or_even {nums : List Int} :
  nums ≠ [] →
  oddest nums = none →
  let oddities := nums.map get_oddity
  let max_odd := oddities.maximum?
  match max_odd with
  | none => True 
  | some m => 
    (oddities.filter (·= m)).length > 1 ∨ m = 0 :=
  sorry

theorem oddest_output_type (nums : List Int) :
  oddest nums = none ∨ (∃ x, oddest nums = some x) :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval oddest [1, 2]

/-
info: 3
-/
-- #guard_msgs in
-- #eval oddest [1, 3]

/-
info: 7
-/
-- #guard_msgs in
-- #eval oddest [1, 3, 5, 7]
-- </vc-theorems>