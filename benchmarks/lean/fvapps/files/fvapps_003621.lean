-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd (a b : Nat) : Nat := sorry

def coprimes (n : Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
def countCoprimes (n : Nat) : Nat :=
  (List.range n).filter (fun x => gcd x n = 1) |>.length

theorem coprimes_all_less (n : Nat) (h : n ≥ 2) :
  ∀ x ∈ coprimes n, x > 0 ∧ x < n :=
sorry
-- </vc-theorems>