-- <vc-preamble>
def canServeIcecream : List Coin → Bool
  := sorry

def countFives (l : List Coin) : Nat :=
  (l.filter (. == Coin.five)).length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countTens (l : List Coin) : Nat :=
  (l.filter (. == Coin.ten)).length
-- </vc-definitions>

-- <vc-theorems>
theorem all_fives_servable {coins : List Coin} (h : ∀ c ∈ coins, c = Coin.five) :
  canServeIcecream coins = true := sorry

theorem start_with_ten_fails {coins : List Coin} (h1 : coins.length > 0) 
  (h2 : ∀ c ∈ coins, c = Coin.ten) :
  canServeIcecream coins = false := sorry

theorem empty_and_base_cases :
  canServeIcecream [] = true ∧
  canServeIcecream [Coin.five] = true ∧
  canServeIcecream [Coin.ten] = false ∧
  canServeIcecream [Coin.fifteen] = false := sorry

theorem valid_service_has_change {coins : List Coin} 
  (h : ∀ c ∈ coins, c = Coin.five ∨ c = Coin.ten ∨ c = Coin.fifteen) :
  canServeIcecream coins = true →
  ∀ p : List Coin, p.isPrefixOf coins →
  match p.getLast? with
  | none => True 
  | some last =>
    if decide (last = Coin.ten)
    then countFives p > 0
    else if decide (last = Coin.fifteen)
    then countTens p > 0 ∨ countFives p ≥ 2
    else True := sorry

theorem invalid_service_lacks_change {coins : List Coin}
  (h : ∀ c ∈ coins, c = Coin.five ∨ c = Coin.ten ∨ c = Coin.fifteen) :
  canServeIcecream coins = false →
  ∃ p : List Coin, p.isPrefixOf coins ∧
  match p.getLast? with
  | none => False
  | some last =>
    (last = Coin.ten ∧ countFives p = 0) ∨ 
    (last = Coin.fifteen ∧ countTens p = 0 ∧ countFives p < 2) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval can_serve_icecream [5, 10]

/-
info: False
-/
-- #guard_msgs in
-- #eval can_serve_icecream [10, 5]

/-
info: False
-/
-- #guard_msgs in
-- #eval can_serve_icecream [5, 15]
-- </vc-theorems>