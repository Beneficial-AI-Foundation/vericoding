-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def relativePrime (n : Nat) (arr : List Int) : List Int := sorry

def isGCD (a b : Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem relatively_prime_subset (n : Nat) (arr : List Int) (x : Int) :
  x ∈ relativePrime n arr → x ∈ arr := sorry

theorem relatively_prime_coprime (n : Nat) (arr : List Int) (x : Int) :
  x ∈ relativePrime n arr → isGCD n x = 1 := sorry

theorem relatively_prime_complete (n : Nat) (arr : List Int) (x : Int) :
  x ∈ arr → isGCD n x = 1 → x ∈ relativePrime n arr := sorry

theorem relatively_prime_empty (n : Nat) :
  relativePrime n [] = [] := sorry

theorem relatively_prime_one (n : Nat) :
  relativePrime n [1] = [1] := sorry
-- </vc-theorems>