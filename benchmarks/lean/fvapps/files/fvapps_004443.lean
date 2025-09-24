-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def common (lst1 lst2 lst3 : List Int) : Int := sorry

theorem common_disjoint (lst : List Int) : 
  lst ≠ [] → 
  let shifted1 := lst.map (· + 10000)
  let shifted2 := lst.map (· + 20000)
  common lst shifted1 shifted2 = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>