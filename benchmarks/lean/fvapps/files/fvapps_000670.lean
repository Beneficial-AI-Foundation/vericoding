-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def canZebrasSpatAtEachOther (positions : List (Int × Int)) : Bool := sorry

theorem canZebrasSpatAtEachOther_returns_bool 
  (positions : List (Int × Int))
  (h1 : positions ≠ []) : 
  canZebrasSpatAtEachOther positions = true ∨ 
  canZebrasSpatAtEachOther positions = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reciprocal_spitting
  {positions : List (Int × Int)}
  {pos1 pos2 dist1 dist2 : Int}
  (h1 : positions = [(pos1, dist1), (pos2, dist2)])
  (h2 : pos1 ≠ pos2)
  (h3 : pos1 + dist1 = pos2)
  (h4 : pos2 + dist2 = pos1) :
  canZebrasSpatAtEachOther positions = true := sorry
-- </vc-theorems>