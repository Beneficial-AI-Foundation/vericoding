-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_lucky (arr : List Nat) : Int := sorry

theorem find_lucky_lower_bound (arr : List Nat) : 
  find_lucky arr ≥ -1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_lucky_freq_match (arr : List Nat) :
  find_lucky arr ≠ -1 → 
  (arr.countP (· = (find_lucky arr).toNat)) = (find_lucky arr).toNat := sorry 

theorem find_lucky_is_max (arr : List Nat) (n : Nat) :
  n ∈ arr → 
  (arr.countP (· = n)) = n →
  n ≤ (find_lucky arr).toNat := sorry
-- </vc-theorems>