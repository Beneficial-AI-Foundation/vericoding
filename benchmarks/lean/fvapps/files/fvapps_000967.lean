-- <vc-preamble>
def get_max_leads (rounds : List (Nat × Nat)) : Nat × Nat :=
  rounds.foldl (fun acc r =>
    let p1Total := acc.1 + r.1
    let p2Total := acc.2 + r.2
    if p1Total > p2Total
    then (p1Total - p2Total, acc.2)
    else (acc.1, p2Total - p1Total)
  ) (0, 0)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_winner_and_max_lead (rounds : List (Nat × Nat)) : Nat × Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem winner_is_valid (rounds : List (Nat × Nat)) :
  let (winner, _) := find_winner_and_max_lead rounds
  winner = 1 ∨ winner = 2 :=
sorry

theorem max_lead_nonnegative (rounds : List (Nat × Nat)) :
  let (_, maxLead) := find_winner_and_max_lead rounds
  maxLead ≥ 0 :=
sorry
-- </vc-theorems>