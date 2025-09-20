-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findShortestPrefix (n : Nat) (arr : List Int) : Nat :=
  sorry

/- Theorem stating that result is always a valid index or 0 -/
-- </vc-definitions>

-- <vc-theorems>
theorem find_shortest_prefix_bounds {n : Nat} {arr : List Int} 
  (h : arr.length = n) (h1 : n > 0) : 
  let result := findShortestPrefix n arr
  0 ≤ result ∧ result < n :=
  sorry
-- </vc-theorems>