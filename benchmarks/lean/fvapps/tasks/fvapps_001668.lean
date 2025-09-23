-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def runoff (voters : List (List Char)) : Option Char := sorry

variable (voters : List (List Char))
-- </vc-definitions>

-- <vc-theorems>
theorem winner_must_be_candidate (voters : List (List Char)) :
  match runoff voters with
  | none => True 
  | some winner => ∀ voter ∈ voters, winner ∈ voter
  := sorry

theorem voters_not_empty (voters : List (List Char)) :
  match runoff voters with
  | none => True
  | some _ => voters.length > 0 ∧ ∀ voter ∈ voters, voter.length > 0
  := sorry

theorem preserves_input (voters : List (List Char)) :
  let original := voters
  let _ := runoff voters
  voters = original := sorry
-- </vc-theorems>