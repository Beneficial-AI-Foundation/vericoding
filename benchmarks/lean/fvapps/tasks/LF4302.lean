-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hop_across (lst : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hop_across_min_hops {lst : List Nat} (h : lst.length > 0) :
  hop_across lst ≥ 2 := sorry

theorem hop_across_symmetric {lst : List Nat} :
  hop_across lst = hop_across lst.reverse := sorry

theorem hop_across_max_hops {lst : List Nat} :
  hop_across lst ≤ 2 * lst.length := sorry

theorem hop_across_single_element {x : Nat} :
  hop_across [x] = 2 := sorry

theorem hop_across_monotone_scaling {lst : List Nat} (h : lst.length ≥ 2) 
  (h_sorted : ∀ i j, i < j → j < lst.length → lst.get ⟨i, sorry⟩ ≤ lst.get ⟨j, sorry⟩) :
  hop_across (lst.map (· * 2)) ≤ hop_across lst := sorry
-- </vc-theorems>