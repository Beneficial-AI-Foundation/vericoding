-- <vc-preamble>
def min_int (a b : Int) : Int := if a ≤ b then a else b

def list_minimum (l : List Int) : Int :=
  match l with
  | [] => 0
  | x :: xs => match xs with
    | [] => x
    | y :: ys => min_int x (list_minimum xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_price (coins : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_price_first_coin_min {coins : List Int} (h : coins.length ≥ 2) :
  coins ≠ [] → coins.head! = list_minimum coins :=
sorry

theorem min_price_result_bounds {coins : List Int} (h : coins.length ≥ 2) :
  let result := min_price coins
  result ≠ -1 → result ≥ coins.head! :=
sorry

theorem min_price_preserves_input {coins : List Int} (h : coins.length ≥ 2) :
  let original := coins
  let _ := min_price coins
  coins = original :=
sorry

theorem coprime_has_solution {coins : List Int} (h : coins.length ≥ 2) :
  Nat.gcd (coins.head!.toNat) (coins.get! 1).toNat = 1 →
  min_price coins ≠ -1 :=
sorry
-- </vc-theorems>