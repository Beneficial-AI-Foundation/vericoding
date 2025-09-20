-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_chopstick_pairs (n : Nat) (d : Nat) (lengths : List Nat) : Nat := sorry

theorem max_chopstick_pairs_non_negative (n : Nat) (d : Nat) (lengths : List Nat)
  (hn : n ≥ 2) (hlen : lengths.length = n) :
  max_chopstick_pairs n d lengths ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_chopstick_pairs_upper_bound (n : Nat) (d : Nat) (lengths : List Nat)
  (hn : n ≥ 2) (hlen : lengths.length = n) :
  max_chopstick_pairs n d lengths ≤ n/2 := sorry

theorem max_chopstick_pairs_permutation_invariant (n : Nat) (d : Nat) (lengths1 lengths2 : List Nat)  
  (hn : n ≥ 2) (hlen1 : lengths1.length = n) (hlen2 : lengths2.length = n)
  (hperm : lengths2.isPerm lengths1) :
  max_chopstick_pairs n d lengths1 = max_chopstick_pairs n d lengths2 := sorry

theorem max_chopstick_pairs_monotone_d (n : Nat) (d : Nat) (lengths : List Nat)
  (hn : n ≥ 2) (hlen : lengths.length = n) (hd : d > 0) :
  max_chopstick_pairs n d lengths ≥ max_chopstick_pairs n (d-1) lengths := sorry
-- </vc-theorems>