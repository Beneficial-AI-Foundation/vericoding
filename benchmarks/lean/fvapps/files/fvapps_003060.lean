-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findPrimesSextuplet (limit : Nat) : List Nat :=
  sorry

def isPrime (n : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem primes_sextuplet_length (limit : Nat) (h : limit ≥ 1000) :
  (findPrimesSextuplet limit).length = 6 :=
sorry

theorem primes_sextuplet_monotone (limit : Nat) (h : limit ≥ 1000) :
  let result := findPrimesSextuplet limit
  ∀ i j, i < j → i < result.length → j < result.length →
  result[i]! < result[j]! :=
sorry

theorem primes_sextuplet_all_prime (limit : Nat) (h : limit ≥ 1000) :
  ∀ x ∈ findPrimesSextuplet limit, isPrime x = true :=
sorry

theorem primes_sextuplet_diffs (limit : Nat) (h : limit ≥ 1000) :
  let result := findPrimesSextuplet limit
  let diffs := List.map (fun p => p.2 - p.1) (List.zip result result.tail)
  diffs = [4,2,4,2,4] :=
sorry
-- </vc-theorems>