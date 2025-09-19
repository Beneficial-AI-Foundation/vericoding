-- <vc-preamble>
def split (s : String) : List String := sorry
def toNat (s : String) : Option Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def scratch (tickets : List String) : Nat := sorry

theorem scratch_non_negative (tickets : List String) : 
  scratch tickets ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>