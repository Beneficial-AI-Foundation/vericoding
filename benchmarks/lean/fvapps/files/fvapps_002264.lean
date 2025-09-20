-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_replacements_for_pairs (n : Nat) (k : Nat) (arr : List Nat) : Nat := sorry

theorem optimal_array {n k : Nat}
  (h1 : n > 1)
  (h2 : n % 2 = 0)
  (h3 : k > 0)
  (h4 : k ≤ 50) :
  let arr := List.replicate (n/2) 1 ++ List.replicate (n/2) k
  min_replacements_for_pairs n k arr = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>