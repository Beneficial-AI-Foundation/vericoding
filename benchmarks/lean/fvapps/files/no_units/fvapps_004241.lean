-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find (seq : List Int) : Int := sorry

theorem find_simple_sequence
    (start : Int) :
    find [start, start + 2, start + 6] = start + 4 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_symmetric_sequence
    (center : Int) :
    find [center - 4, center - 2, center + 2, center + 4] = center := sorry
-- </vc-theorems>