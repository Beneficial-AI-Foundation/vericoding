-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gains_adds (n1 n2 : Nat) :
  calculate s!"Someone has {n1} items and gains {n2}" = n1 + n2 := by
  sorry

theorem loses_subtracts (n1 n2 : Nat) :
  calculate s!"Someone has {n1} items and loses {n2}" = n1 - n2 := by
  sorry

theorem calculate_properties (n1 n2 : Nat) (op : String) 
  (h : op = "gains" ∨ op = "loses") :
  calculate s!"Someone has {n1} items and {op} {n2}" = 
    if op = "gains" 
    then n1 + n2
    else n1 - n2 := by
  sorry

/-
info: 44
-/
-- #guard_msgs in
-- #eval calculate "Panda has 48 apples and loses 4"

/-
info: 40
-/
-- #guard_msgs in
-- #eval calculate "Jerry has 34 apples and gains 6"

/-
info: 35
-/
-- #guard_msgs in
-- #eval calculate "Tom has 20 apples and gains 15"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded