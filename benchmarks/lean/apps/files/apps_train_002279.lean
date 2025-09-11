-- <vc-preamble>
def solve_candy_gift (n : Nat) (candies : List Nat) : Nat :=
  sorry

def count_occurrences (a : Nat) (l : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def frequency_list (l : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_candy_gift_bounded 
  (n : Nat) (candies : List Nat)
  (h1 : n = candies.length)
  (h2 : ∀ x ∈ candies, 1 ≤ x ∧ x ≤ 1000) :
  solve_candy_gift n candies ≤ n := 
  sorry

theorem solve_candy_gift_nonnegative
  (n : Nat) (candies : List Nat)
  (h1 : n = candies.length)
  (h2 : ∀ x ∈ candies, 1 ≤ x ∧ x ≤ 1000) :
  0 ≤ solve_candy_gift n candies :=
  sorry

theorem solve_candy_gift_monotonic_frequencies
  (n : Nat) (candies : List Nat)
  (h1 : n = candies.length)
  (h2 : ∀ x ∈ candies, 1 ≤ x ∧ x ≤ 1000) :
  let freqs := frequency_list candies
  let result := solve_candy_gift n candies
  ∀ i j, i < j → i < freqs.length → j < freqs.length →
  let take_i := if i = 0 then result else min ((freqs.get! (i-1))-1) (freqs.get! i)
  let take_j := if j = 0 then result else min ((freqs.get! (j-1))-1) (freqs.get! j)
  take_i ≥ take_j :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_candy_gift 8 [1, 4, 8, 4, 5, 6, 3, 8]

/-
info: 10
-/
-- #guard_msgs in
-- #eval solve_candy_gift 16 [2, 1, 3, 3, 4, 3, 4, 4, 1, 3, 2, 2, 2, 4, 1, 1]

/-
info: 9
-/
-- #guard_msgs in
-- #eval solve_candy_gift 9 [2, 2, 4, 4, 4, 7, 7, 7, 7]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded