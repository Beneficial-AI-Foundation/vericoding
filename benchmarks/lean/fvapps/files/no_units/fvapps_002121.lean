-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_money_events (n : Nat) (balances : List Int) (events : List (Nat × Int)) : List Int := sorry

def solve_money_events_multi (n : Nat) (balances : List Int) (events : List (Nat × Nat × Int)) : List Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_events_preserves_balances (n : Nat) (h : n ≥ 1) (balances : List Int) : 
  solve_money_events n balances [] = balances := sorry

theorem single_payout_distributes_evenly (n : Nat) (amount : Int) (h1 : n ≥ 1) (h2 : n ≤ 100) (h3 : amount ≥ 0) (h4 : amount ≤ 1000) :
  let balances := List.replicate n 0
  let events := [(2, amount)]
  let result := solve_money_events n balances events
  ∀ x ∈ result, x = amount := sorry

theorem single_receipt_maintains_minimum (n person : Nat) (amount : Int) 
  (h1 : n ≥ 1) (h2 : n ≤ 10) (h3 : person ≥ 1) (h4 : person ≤ n) 
  (h5 : amount ≥ 0) (h6 : amount ≤ 1000) :
  let balances := List.replicate n 0
  let events := [(1, person, amount)]
  let result := solve_money_events_multi n balances events
  List.get! result (person - 1) ≥ amount := sorry
-- </vc-theorems>