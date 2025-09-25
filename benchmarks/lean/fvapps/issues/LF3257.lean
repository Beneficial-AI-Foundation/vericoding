-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lowest_temp (s : String) : Option Int := sorry 

theorem lowest_temp_empty: lowest_temp "" = none := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lowest_temp_single (n : Int) (h : -100 ≤ n ∧ n ≤ 100) :
  lowest_temp (toString n) = some n := sorry

theorem lowest_temp_properties (s : String) :
  match lowest_temp s with
  | none => s = ""
  | some result =>
    ∃ nums : List Int,
      (∀ n ∈ nums, -100 ≤ n ∧ n ≤ 100) ∧
      result = nums.minimum?.get! ∧
      nums ≠ []
  := sorry

/-
info: None
-/
-- #guard_msgs in
-- #eval lowest_temp ""

/-
info: -8
-/
-- #guard_msgs in
-- #eval lowest_temp "-1 50 -4 20 22 -7 0 10 -8"

/-
info: 5
-/
-- #guard_msgs in
-- #eval lowest_temp "5"
-- </vc-theorems>