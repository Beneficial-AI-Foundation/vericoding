def isPrime (n : Nat) : Bool := sorry

def sqrt (n : Int) : Int := sorry

def big_primefac_div (n : Int) : Option (Int × Int) := sorry

def abs (n : Int) : Int := sorry

-- <vc-helpers>
-- </vc-helpers>

def isInteger (n : Int) : Bool := sorry 

theorem big_primefac_div_int_valid {n : Int}
  (h : 2 ≤ n) (h2 : n ≤ 10^6) :
  if isInteger n then
    match big_primefac_div n with
    | none => True
    | some (p, d) => p > 0 ∧ d > 0
  else
    big_primefac_div n = none := sorry

theorem big_primefac_div_valid_pos_int {n : Int} 
  (h : 2 ≤ n) (h2 : n ≤ 10^6) :
  match big_primefac_div n with
  | none => ∀ i, 2 ≤ i → i ≤ sqrt n → ¬(n % i = 0)  
  | some (p, d) => 
    1 < p ∧ 1 < d ∧ 
    n % p = 0 ∧ n % d = 0 := sorry

theorem big_primefac_div_neg {n : Int}
  (h : -10^6 ≤ n) (h2 : n ≤ -2) :
  big_primefac_div n = big_primefac_div (abs n) := sorry

/-
info: [5, 50]
-/
-- #guard_msgs in
-- #eval big_primefac_div 100

/-
info: []
-/
-- #guard_msgs in
-- #eval big_primefac_div 997

/-
info: [5, 900]
-/
-- #guard_msgs in
-- #eval big_primefac_div -1800.0

-- Apps difficulty: introductory
-- Assurance level: unguarded