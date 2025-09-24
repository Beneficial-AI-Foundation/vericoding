-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_triples (n1 n2 n3 : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_triples_nonnegative (n1 n2 n3 : Nat) :
  n1 > 0 → n2 > 0 → n3 > 0 → 
  let result := count_triples n1 n2 n3
  result ≥ 0 ∧ result < 1000000007 :=
sorry
-- </vc-theorems>