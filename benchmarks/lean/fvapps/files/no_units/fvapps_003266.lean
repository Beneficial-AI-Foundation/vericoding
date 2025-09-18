-- <vc-preamble>
def sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + sum xs

def isSorted : List Nat → Bool
  | [] => true
  | [_] => true
  | x::y::rest => x ≤ y && isSorted (y::rest)

def countUnique : List Nat → Nat 
  | [] => 0
  | x::xs => if xs.contains x then countUnique xs else 1 + countUnique xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def powers (n: Nat) : List Nat := sorry

def isPowerOfTwo (n: Nat) : Bool := 
  n != 0 && n &&& (n - 1) == 0
-- </vc-definitions>

-- <vc-theorems>
theorem powers_sum_equals_input (n: Nat) (h: n > 0) : 
  sum (powers n) = n := sorry

theorem powers_are_powers_of_two (n: Nat) (h: n > 0) :
  ∀ p ∈ powers n, isPowerOfTwo p = true := sorry

theorem powers_are_sorted (n: Nat) (h: n > 0) :
  isSorted (powers n) = true := sorry

theorem powers_are_unique (n: Nat) (h: n > 0) :
  (powers n).length = countUnique (powers n) := sorry
-- </vc-theorems>