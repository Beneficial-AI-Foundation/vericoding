-- <vc-preamble>
def min_candies_for_party (people_counts: List Nat) (remainder: Nat) : Nat := sorry

def gcd (a b : Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lcm (a b : Nat) : Nat := Nat.div (a * b) (gcd a b)

theorem remainder_divides_result (people_counts: List Nat) (remainder: Nat) (count: Nat)
  (h: count ∈ people_counts) (h2: count > 0) :
  count ∣ (min_candies_for_party people_counts remainder - remainder) := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 7
-/
-- #guard_msgs in
-- #eval min_candies_for_party [2, 3] 1

/-
info: 13
-/
-- #guard_msgs in
-- #eval min_candies_for_party [2, 4, 6] 1

/-
info: 7
-/
-- #guard_msgs in
-- #eval min_candies_for_party [5] 2
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible