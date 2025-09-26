-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def length_sup_u_k (n : Nat) (k : Nat) : Nat :=
  sorry

def comp (n : Nat) : Nat :=
  sorry

def u1 : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_sup_u_k_bounds (n k : Nat) (h : n > 0) :
  0 ≤ length_sup_u_k n k ∧ length_sup_u_k n k ≤ n :=
sorry

theorem comp_bounds (n : Nat) (h : n > 1) :
  0 ≤ comp n ∧ comp n ≤ n - 1 :=
sorry

theorem comp_deterministic (n : Nat) :
  comp n = comp n :=
sorry
-- </vc-theorems>