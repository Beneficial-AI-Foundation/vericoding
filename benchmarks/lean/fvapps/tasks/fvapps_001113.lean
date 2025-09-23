-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_markets (n : Nat) (m : Nat) (edges : List (Nat × Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_markets_bounds (n : Nat) (m : Nat) (edges : List (Nat × Nat))
  (h1 : n > 0)
  (h2 : ∀ (e : Nat × Nat), e ∈ edges → e.1 < n ∧ e.2 < n)
  (h3 : ∀ (e : Nat × Nat), e ∈ edges → e.1 ≠ e.2) :
  1 ≤ count_markets n m edges ∧ count_markets n m edges ≤ n := sorry

theorem empty_graph_markets (n : Nat) (h : n > 0) :
  count_markets n 0 [] = n := sorry

theorem path_graph_one_market (n : Nat) (h : n > 0) :
  count_markets n (n-1) (List.range (n-1) |>.map (λ i => (i, i+1))) = 1 := sorry

theorem isolated_vertices (n : Nat) (h : n > 0) :
  count_markets n 0 [] = n := sorry

theorem cycle_one_market (n : Nat) (h : n ≥ 2) :
  count_markets n n (List.range n |>.map (λ i => (i, (i+1) % n))) = 1 := sorry
-- </vc-theorems>