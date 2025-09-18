-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hydrate (s : String) : String := sorry 

/- For a single digit input, the function hydrate returns a string with the 
    same number of glasses of water, and uses "glass" for 1 and "glasses" otherwise -/
-- </vc-definitions>

-- <vc-theorems>
theorem hydrate_single_digit {n : Nat} (h : n ≤ 9) : 
  hydrate s!"{n} drinks" = 
    s!"{n} {if n = 1 then "glass" else "glasses"} of water" := 
  sorry
-- </vc-theorems>