-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def elections_winners (votes: List Nat) (k: Nat) : Nat :=
  sorry

def list_maximum (l: List Nat) (h: l.length > 0) : Nat :=
  sorry

def list_minimum (l: List Nat) (h: l.length > 0) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem elections_winners_properties_result_bounds
  (votes: List Nat) (k: Nat) (h: votes.length > 0) :
  let result := elections_winners votes k
  0 ≤ result ∧ result ≤ votes.length :=
sorry

theorem elections_winners_k_zero_result
  (votes: List Nat) (h: votes.length > 0) :
  let result := elections_winners votes 0
  result = 0 ∨ result = 1 :=
sorry
-- </vc-theorems>