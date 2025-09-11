-- <vc-preamble>
def is_bouncy (n : Nat) : Bool := sorry

def digits_sorted (n : Nat) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digits_sorted_reverse (n : Nat) : Bool := sorry

theorem small_numbers_not_bouncy (n : Nat) (h : n < 100) : 
  ¬ is_bouncy n := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible