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
-- </vc-theorems>