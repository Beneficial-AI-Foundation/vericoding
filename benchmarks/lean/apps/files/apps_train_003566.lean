def goldbach_partitions : Nat → List String := sorry

def is_prime : Nat → Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def Nat.is_even (n : Nat) : Bool := n % 2 == 0

theorem goldbach_odd_numbers_empty (n : Nat) :
  n % 2 = 1 → goldbach_partitions n = [] := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible