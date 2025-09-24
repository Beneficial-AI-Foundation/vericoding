-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPeek (v : Array Int) (i : Nat) : Bool :=
sorry

def mPeekSum (v : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
partial def peekSum (v : Array Int) (i : Nat) : Int :=
if i = 0 then 0
else if isPeek v (i-1) then v[i-1]! + peekSum v (i-1)
else peekSum v (i-1)

theorem mPeekSum_spec (v : Array Int) :
v.size > 0 → mPeekSum v = peekSum v v.size :=
sorry
-- </vc-theorems>