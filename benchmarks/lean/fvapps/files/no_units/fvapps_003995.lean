-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def spin_solve (s : String) : String := sorry

def countChar (s : String) (c : Char) : Nat := 
  s.foldl (fun acc x => if x = c then acc + 1 else acc) 0

/- The output of spin_solve is always a string -/
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_string (s : String) :
  ∃ (result : String), spin_solve s = result := sorry
-- </vc-theorems>