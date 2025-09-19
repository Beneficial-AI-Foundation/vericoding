-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CombString := String -- represents strings of only * and .

def combs (a b : CombString) : Nat := sorry

/- The result length is at least as long as the longest input -/
-- </vc-definitions>

-- <vc-theorems>
theorem combs_min_length {a b : CombString} :
  combs a b ≥ max a.length b.length := sorry
-- </vc-theorems>