-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cycle (s : List Int) : List Int := sorry

theorem cycle_empty_for_short_sequences {s : List Int} 
  (h : s.length ≤ 1) :
  cycle s = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>