-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPrime (n : Nat) : Bool :=
sorry

def sqrt (n : Int) : Int :=
sorry

def big_primefac_div (n : Int) : Option (Int × Int) :=
sorry

def abs (n : Int) : Int :=
sorry

def isInteger (n : Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem big_primefac_div_int_valid {n : Int}
  (h : 2 ≤ n) (h2 : n ≤ 10^6) :
  if isInteger n then
    match big_primefac_div n with
    | none => True
    | some (p, d) => p > 0 ∧ d > 0
  else
    big_primefac_div n = none :=
sorry

theorem big_primefac_div_valid_pos_int {n : Int}
  (h : 2 ≤ n) (h2 : n ≤ 10^6) :
  match big_primefac_div n with
  | none => ∀ i, 2 ≤ i → i ≤ sqrt n → ¬(n % i = 0)
  | some (p, d) =>
    1 < p ∧ 1 < d ∧
    n % p = 0 ∧ n % d = 0 :=
sorry

theorem big_primefac_div_neg {n : Int}
  (h : -10^6 ≤ n) (h2 : n ≤ -2) :
  big_primefac_div n = big_primefac_div (abs n) :=
sorry
-- </vc-theorems>