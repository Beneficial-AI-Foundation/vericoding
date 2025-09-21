-- <vc-preamble>
def countTo (a : Array Bool) (n : Nat) : Int :=
if n = 0 then 0
else countTo a (n-1) + (if a[n-1]! then 1 else 0)

def CountTrue (a : Array Bool) : Int :=
countTo a a.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem countTo_spec (a : Array Bool) (n : Nat) :
n ≥ 0 ∧ n ≤ a.size →
countTo a n ≥ 0 :=
sorry

theorem CountTrue_spec (a : Array Bool) :
CountTrue a = countTo a a.size :=
sorry
-- </vc-theorems>