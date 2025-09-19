-- <vc-preamble>
def coprimes (n : Nat) : List Nat := sorry

def gcd (a b : Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countCoprimes (n : Nat) : Nat :=
  (List.range n).filter (fun x => gcd x n = 1) |>.length
-- </vc-definitions>

-- <vc-theorems>
theorem coprimes_all_less (n : Nat) (h : n ≥ 2) :
  ∀ x ∈ coprimes n, x > 0 ∧ x < n := sorry
-- </vc-theorems>