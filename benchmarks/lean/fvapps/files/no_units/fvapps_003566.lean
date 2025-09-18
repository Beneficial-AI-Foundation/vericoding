-- <vc-preamble>
def goldbach_partitions : Nat → List String := sorry

def is_prime : Nat → Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Nat.is_even (n : Nat) : Bool := n % 2 == 0

theorem goldbach_odd_numbers_empty (n : Nat) :
  n % 2 = 1 → goldbach_partitions n = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>