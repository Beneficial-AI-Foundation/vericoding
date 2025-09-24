-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isWinner (ticket : List (String × Nat)) (win : Nat) : String := sorry

theorem bingo_result_valid (ticket : List (String × Nat)) (win : Nat) :
  win ≥ 0 → ticket.length > 0 → ticket.length ≤ 10 → 
  (isWinner ticket win = "Winner!" ∨ isWinner ticket win = "Loser!") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bingo_matches_determine_win (ticket : List (String × Nat)) (win : Nat) : 
  win ≥ 0 → ticket.length > 0 → ticket.length ≤ 10 →
  (let m := (ticket.filter (fun p => p.1.any (fun c => c = Char.ofNat p.2))).length;
  isWinner ticket win = (if m ≥ win then "Winner!" else "Loser!")) := sorry

theorem bingo_zero_always_wins (ticket : List (String × Nat)) :
  ticket.length > 0 → ticket.length ≤ 10 →
  isWinner ticket 0 = "Winner!" := sorry

theorem bingo_impossible_win (ticket : List (String × Nat)) :
  ticket.length > 0 → ticket.length ≤ 10 →
  isWinner ticket (ticket.length + 1) = "Loser!" := sorry
-- </vc-theorems>