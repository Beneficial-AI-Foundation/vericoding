-- <vc-preamble>
def find_winner_and_max_lead (rounds : List (Nat × Nat)) : Nat × Nat :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_max_leads (rounds : List (Nat × Nat)) : Nat × Nat :=
  rounds.foldl (fun acc r =>
    let p1Total := acc.1 + r.1
    let p2Total := acc.2 + r.2
    if p1Total > p2Total 
    then (p1Total - p2Total, acc.2)
    else (acc.1, p2Total - p1Total)
  ) (0, 0)
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

/-
info: (1, 58)
-/
-- #guard_msgs in
-- #eval find_winner_and_max_lead [(140, 82), (89, 134), (90, 110), (112, 106), (88, 90)]

/-
info: (1, 15)
-/
-- #guard_msgs in
-- #eval find_winner_and_max_lead [(10, 5), (20, 15), (30, 25)]

/-
info: (2, 15)
-/
-- #guard_msgs in
-- #eval find_winner_and_max_lead [(5, 10), (15, 20), (25, 30)]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible