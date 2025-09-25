-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def areKidsHappy (n : Nat) (x : Nat) (candies : List Nat) : String := sorry

theorem output_is_yes_or_no {n x : Nat} {candies : List Nat}
  (h1 : n ≥ 2) (h2 : n ≤ 100) 
  (h3 : x ≥ 1) (h4 : x ≤ 1000)
  (h5 : candies.length ≥ 2) (h6 : candies.length ≤ 100)
  (h7 : ∀ c ∈ candies, c ≥ 1 ∧ c ≤ 1000) :
  areKidsHappy n x candies = "YES" ∨ areKidsHappy n x candies = "NO" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem happy_condition {n x : Nat} {candies : List Nat}
  (h1 : n ≥ 2) (h2 : n ≤ 100)
  (h3 : x ≥ 1) (h4 : x ≤ 1000)
  (h5 : candies.length ≥ 2) (h6 : candies.length ≤ 100)
  (h7 : ∀ c ∈ candies, c ≥ 1 ∧ c ≤ 1000) :
  (candies.maximum? >>= λ max => candies.minimum? >>= λ min => some (max - min < x)) = some true ↔ 
  areKidsHappy n x candies = "YES" := sorry

theorem identical_candies_are_happy {candies : List Nat} {n x : Nat}
  (h1 : candies.length ≥ 2) (h2 : candies.length ≤ 100)
  (h3 : ∀ c ∈ candies, c ≥ 1 ∧ c ≤ 1000)
  (h4 : ∀ i : Fin candies.length, ∀ j : Fin candies.length, candies.get i = candies.get j)
  (h5 : x = 1)
  (h6 : n = candies.length) :
  areKidsHappy n x candies = "YES" := sorry

/-
info: 'NO'
-/
-- #guard_msgs in
-- #eval are_kids_happy 5 6 [3, 5, 6, 8, 1]

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval are_kids_happy 3 10 [5, 2, 9]

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval are_kids_happy 4 5 [1, 2, 3, 4]
-- </vc-theorems>