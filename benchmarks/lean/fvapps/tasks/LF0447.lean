-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def coin_change (coins : List Nat) (amount : Nat) : Int := sorry

def list_min : List Nat → Nat 
| [] => 0
| [x] => x
| (x::xs) => Nat.min x (list_min xs)
-- </vc-definitions>

-- <vc-theorems>
theorem coin_change_valid_output {coins : List Nat} {amount : Nat}
  (h1 : coins.length > 0)
  (h2 : ∀ x ∈ coins, x > 0 ∧ x ≤ 20) :
  let result := coin_change coins amount
  result ≥ -1 ∧ (result ≠ -1 → result ≤ amount) := sorry

theorem coin_change_zero_amount {coins : List Nat}
  (h1 : coins.length > 0)
  (h2 : ∀ x ∈ coins, x > 0 ∧ x ≤ 20) :
  coin_change coins 0 = 0 := sorry

theorem coin_change_impossible_amount {coins : List Nat}
  (h1 : coins.length > 0)
  (h2 : ∀ x ∈ coins, x ≥ 2 ∧ x ≤ 20) :
  coin_change coins 1 = -1 := sorry

theorem coin_change_min_coin {coins : List Nat}
  (h1 : coins.length > 0)
  (h2 : ∀ x ∈ coins, x > 0 ∧ x ≤ 20)
  (h3 : list_min coins > 1) :
  coin_change coins (list_min coins - 1) = -1 := sorry
-- </vc-theorems>