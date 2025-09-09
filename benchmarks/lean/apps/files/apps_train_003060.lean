def findPrimesSextuplet (limit : Nat) : List Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def isPrime (n : Nat) : Bool :=
  sorry

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

/-
info: [7, 11, 13, 17, 19, 23]
-/
-- #guard_msgs in
-- #eval find_primes_sextuplet 70

/-
info: [97, 101, 103, 107, 109, 113]
-/
-- #guard_msgs in
-- #eval find_primes_sextuplet 600

/-
info: [1091257, 1091261, 1091263, 1091267, 1091269, 1091273]
-/
-- #guard_msgs in
-- #eval find_primes_sextuplet 2000000

-- Apps difficulty: introductory
-- Assurance level: guarded