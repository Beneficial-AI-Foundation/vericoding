-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def trap (heights : List Nat) : Nat := sorry

theorem trap_empty : 
  trap [] = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem trap_singleton (h : Nat) :
  trap [h] = 0 := sorry

theorem trap_valley (h : Nat) :
  h > 0 → trap [h, 0, h] = h := sorry
-- </vc-theorems>