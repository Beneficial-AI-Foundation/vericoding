-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def optimalNumberOfCoins (n : Nat) (coins : List Nat) : Option Nat := sorry

theorem optimal_coins_properties
    (n : Nat)
    (coins : List Nat)
    (h1 : n ≥ 1)
    (h2 : n ≤ 1000)
    (h3 : ∀ c ∈ coins, c ≥ 1 ∧ c ≤ 100)
    (h4 : coins.length ≥ 1)
    (h5 : coins.length ≤ 10) : 
    match optimalNumberOfCoins n coins with
    | none => True
    | some r => 
        r ≥ 0 ∧
        (1 ∈ coins → r ≤ n) ∧
        (∀ c ∈ coins, n % c = 0 → r ≤ n / c)
    := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem optimal_coins_zero
    (coins : List Nat)
    (h1 : coins.length ≥ 1)
    (h2 : coins.length ≤ 10)
    (h3 : ∀ c ∈ coins, c ≥ 1 ∧ c ≤ 100) :
    optimalNumberOfCoins 0 coins = some 0 := sorry

theorem optimal_coins_edge_cases :
    optimalNumberOfCoins 1 [1] = some 1 ∧
    optimalNumberOfCoins 1 [2] = none := sorry
-- </vc-theorems>