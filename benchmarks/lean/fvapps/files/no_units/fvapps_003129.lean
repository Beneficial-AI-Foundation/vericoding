-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def primes_a_p (lower upper : Nat) : List (List Nat) := sorry

def is_valid_ap (seq : List Nat) (lower upper : Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem primes_ap_increasing_order {lower upper : Nat} (h : lower ≤ upper) :
  let result := primes_a_p lower upper 
  ∀ i j, i < j → List.get! result i ≤ List.get! result j := sorry

theorem primes_ap_length_six {lower upper : Nat} (h : lower ≤ upper) :
  let result := primes_a_p lower upper
  ∀ seq ∈ result, seq.length = 6 := sorry

theorem primes_ap_in_bounds {lower upper : Nat} (h : lower ≤ upper) :
  let result := primes_a_p lower upper
  ∀ seq ∈ result, ∀ x ∈ seq, lower ≤ x ∧ x ≤ upper := sorry

theorem primes_ap_valid_progression {lower upper : Nat} (h : lower ≤ upper) :
  let result := primes_a_p lower upper
  ∀ seq ∈ result, is_valid_ap seq lower upper = true := sorry
-- </vc-theorems>