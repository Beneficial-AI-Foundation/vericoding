-- <vc-preamble>
def totient (n : Int) : Int := sorry

def gcd (a b : Int) : Int := sorry

def isPrime (n : Int) : Bool := sorry

def isInt (n : Int) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countCoprimes (n : Int) : Int := sorry

theorem totient_matches_coprime_count (n : Int) (h : n > 0) :
  totient n = countCoprimes n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem totient_invalid_inputs (n : Int) (h : n ≤ 0) :
  totient n = 0 := sorry

theorem totient_multiplicative (n₁ n₂ : Int) (h₁ : gcd n₁ n₂ = 1) (h₂ : n₁ > 0) (h₃ : n₂ > 0) :
  totient (n₁ * n₂) = totient n₁ * totient n₂ := sorry

theorem totient_prime (p : Int) (h₁ : p > 1) (h₂ : isPrime p) :
  totient p = p - 1 := sorry
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded