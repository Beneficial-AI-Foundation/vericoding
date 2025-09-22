-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def primePalindrome (n : Nat) : Nat :=
  sorry

def isPalindrome (n : Nat) : Bool :=
  sorry

def isPrime (n : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem primePalindrome_geq_input
  (n : Nat)
  (h1 : n ≥ 2)
  (h2 : n ≤ 19990) :
  primePalindrome n ≥ n :=
sorry
-- </vc-theorems>