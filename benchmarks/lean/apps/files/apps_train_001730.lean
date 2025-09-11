-- <vc-preamble>
def min_price (coins : List Int) : Int := sorry

def min_int (a b : Int) : Int := if a ≤ b then a else b
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_minimum (l : List Int) : Int :=
  match l with
  | [] => 0
  | x :: xs => match xs with
    | [] => x
    | y :: ys => min_int x (list_minimum xs)

-- First coin must be minimum of input list
-- </vc-definitions>

-- <vc-theorems>
theorem min_price_first_coin_min {coins : List Int} (h : coins.length ≥ 2) :
  coins ≠ [] → coins.head! = list_minimum coins := sorry

-- Result must be either -1 or >= first coin

theorem min_price_result_bounds {coins : List Int} (h : coins.length ≥ 2) :
  let result := min_price coins
  result ≠ -1 → result ≥ coins.head! := sorry

-- Input list should not be modified after operation

theorem min_price_preserves_input {coins : List Int} (h : coins.length ≥ 2) :
  let original := coins
  let _ := min_price coins
  coins = original := sorry

-- Two coprime numbers should always have a solution

theorem coprime_has_solution {coins : List Int} (h : coins.length ≥ 2) :
  Nat.gcd (coins.head!.toNat) (coins.get! 1).toNat = 1 →
  min_price coins ≠ -1 := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval min_price [3, 5]

/-
info: -1
-/
-- #guard_msgs in
-- #eval min_price [4, 6]

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_price [2, 3]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded