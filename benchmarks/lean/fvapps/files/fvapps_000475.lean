-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def A := List Nat 
def min_k_bit_flips (A : List Nat) (K : Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_k_bit_flips_nonnegative_when_possible 
  (A : List Nat) (K : Nat) :
  let result := min_k_bit_flips A K
  (result ≠ -1) → result ≥ 0 :=
  sorry

theorem min_k_bit_flips_bounded_by_length
  (A : List Nat) (K : Nat) :
  let result := min_k_bit_flips A K
  (result ≠ -1) → result ≤ (List.length A) :=
  sorry 

theorem min_k_bit_flips_k_equals_one_possible
  (A : List Nat) :
  let result := min_k_bit_flips A 1
  result ≥ 0 :=
  sorry
-- </vc-theorems>