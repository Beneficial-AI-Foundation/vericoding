-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_ways (n k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_ways_positive {n k : Nat} (h1 : n ≥ 1) (h2 : k ≥ 1) : 
  count_ways n k ≥ 1 :=
  sorry

theorem count_ways_k_one {n : Nat} (h : n ≥ 1) :
  count_ways n 1 = 1 :=
  sorry

theorem count_ways_k_geq_n {n k : Nat} (h1 : n ≥ 1) (h2 : k ≥ n) :
  count_ways n k = count_ways n n :=
  sorry
-- </vc-theorems>