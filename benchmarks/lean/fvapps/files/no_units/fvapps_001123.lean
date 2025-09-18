-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def determine_winner (sequence : String) : String := sorry

theorem determine_winner_output_valid (sequence : String) : 
  sequence.data.all (fun c => c = 'm' ∨ c = 's') → 
  (determine_winner sequence = "mongooses" ∨ 
   determine_winner sequence = "snakes" ∨ 
   determine_winner sequence = "tie") :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem determine_winner_empty :
  determine_winner "" = "tie" :=
sorry

theorem determine_winner_only_mongooses (sequence : String) :
  sequence.data.all (fun c => c = 'm') →
  sequence.length > 0 →
  determine_winner sequence = "mongooses" :=
sorry

theorem determine_winner_only_mongooses_empty (sequence : String) :
  sequence.data.all (fun c => c = 'm') →
  sequence.length = 0 →
  determine_winner sequence = "tie" :=
sorry

theorem determine_winner_only_snakes (sequence : String) :
  sequence.data.all (fun c => c = 's') →
  sequence.length > 0 →
  determine_winner sequence = "snakes" :=
sorry

theorem determine_winner_only_snakes_empty (sequence : String) :
  sequence.data.all (fun c => c = 's') →
  sequence.length = 0 →
  determine_winner sequence = "tie" :=
sorry

theorem determine_winner_adjacent_valid (sequence : String) :
  sequence.data.all (fun c => c = 'm' ∨ c = 's') →
  sequence.length ≥ 2 →
  (determine_winner sequence = "mongooses" ∨ 
   determine_winner sequence = "snakes" ∨ 
   determine_winner sequence = "tie") :=
sorry
-- </vc-theorems>