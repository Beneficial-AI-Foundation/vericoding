-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def parse (s : String) : List Int := sorry

def countChar (s : String) (c : Char) : Nat := 
  s.toList.filter (· = c) |>.length
-- </vc-definitions>

-- <vc-theorems>
theorem parse_output_bounded (s : String) :
  ∀ x ∈ parse s, x ≥ -s.length
  := sorry
-- </vc-theorems>