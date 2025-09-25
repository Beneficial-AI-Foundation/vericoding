-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_robin_hood (n : Nat) (k : Nat) (coins : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_robin_hood_properties 
  {n : Nat} {k : Nat} {coins : List Nat} 
  (h1 : n ≥ 1) (h2 : n = coins.length) (h3 : ∀ x, x ∈ coins → x ≥ 1) :
  let result := solve_robin_hood n k coins
  (result ≥ 0) ∧ 
  (result ≤ coins.maximum?.getD 0 - coins.minimum?.getD 0) :=
sorry

theorem equal_coins_gives_zero
  {n : Nat} {k : Nat} {coins : List Nat}
  (h1 : n ≥ 1) (h2 : n = coins.length) (h3 : ∀ x, x ∈ coins → x ≥ 1)
  (h4 : ∀ x y, x ∈ coins → y ∈ coins → x = y) :
  solve_robin_hood n k coins = 0 :=
sorry

theorem zero_k_maintains_difference
  {n : Nat} {coins : List Nat}
  (h1 : n ≥ 2) (h2 : n = coins.length) (h3 : ∀ x, x ∈ coins → x ≥ 1) :
  solve_robin_hood n 0 coins = coins.maximum?.getD 0 - coins.minimum?.getD 0 :=
sorry

theorem larger_k_gives_smaller_difference
  {n : Nat} {coins : List Nat}
  (h1 : n ≥ 1) (h2 : n = coins.length) (h3 : ∀ x, x ∈ coins → x ≥ 1)
  {k1 k2 : Nat} (h4 : k2 > k1) :
  solve_robin_hood n k2 coins ≤ solve_robin_hood n k1 coins :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_robin_hood 4 1 [1, 1, 4, 2]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_robin_hood 3 1 [2, 2, 2]

/-
info: 999999943
-/
-- #guard_msgs in
-- #eval solve_robin_hood 4 42 [1, 1, 1, 1000000000]
-- </vc-theorems>