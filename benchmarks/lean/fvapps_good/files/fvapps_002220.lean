-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_max_happiness (N M : Nat) (distances : List Nat) (deliciousness : List (List Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_happiness_nonnegative (N M : Nat) (distances : List Nat) (deliciousness : List (List Nat)) :
  calc_max_happiness N M distances deliciousness ≥ 0 := sorry

theorem max_happiness_is_nat (N M : Nat) (distances : List Nat) (deliciousness : List (List Nat)) :
  ∃ n : Nat, calc_max_happiness N M distances deliciousness = n := sorry

theorem zero_deliciousness_gives_zero (N M : Nat) (distances : List Nat) (deliciousness : List (List Nat))
  (h1 : N > 0)
  (h2 : M > 0)
  (h3 : distances.length = N - 1)
  (h4 : deliciousness.length = N)
  (h5 : ∀ l ∈ deliciousness, l.length = M) 
  (h6 : ∀ l ∈ deliciousness, ∀ x ∈ l, x = 0) :
  calc_max_happiness N M distances deliciousness = 0 := sorry

theorem doubled_distances_decrease_happiness (N M : Nat) (distances : List Nat) (deliciousness : List (List Nat)) 
  (doubled_distances : List Nat)
  (h : doubled_distances = distances.map (· * 2)) :
  calc_max_happiness N M doubled_distances deliciousness ≤ calc_max_happiness N M distances deliciousness := sorry
-- </vc-theorems>