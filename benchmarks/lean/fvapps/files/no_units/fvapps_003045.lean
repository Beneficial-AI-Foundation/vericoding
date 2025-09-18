-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def guess_it (n : Int) (m : Int) : List (List Int) := sorry

def allPos (xs : List Int) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem m_zero_zero :
  guess_it 0 0 = [[0,0,0]] := sorry

theorem zero_one :
  guess_it 0 1 = [] := sorry
-- </vc-theorems>