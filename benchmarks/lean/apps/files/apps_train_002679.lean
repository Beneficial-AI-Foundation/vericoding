-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate (s : String) : String := sorry

theorem calculate_plus_list (nums : List Int) (h : nums ≠ []) : 
  toString (nums.foldl Int.add 0) = 
  calculate (String.intercalate "plus" (nums.map toString)) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: '10'
-/
-- #guard_msgs in
-- #eval calculate "1plus2plus3plus4"

/-
info: '-8'
-/
-- #guard_msgs in
-- #eval calculate "1minus2minus3minus4"

/-
info: '-1'
-/
-- #guard_msgs in
-- #eval calculate "1plus2minus3plus4minus5"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded