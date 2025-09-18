-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD : Nat := 998244353

def solve (N : Nat) (K : Nat) (A : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_length {N K : Nat} {A : List Nat} 
  (h1 : N ≥ 2) (h2 : K ≥ 1) (h3 : A.length = N) :
  (solve N K A).length = K := sorry

theorem solve_mod {N K : Nat} {A : List Nat} 
  (h1 : N ≥ 2) (h2 : K ≥ 1) (h3 : A.length = N) :
  ∀ x ∈ solve N K A, 0 ≤ x ∧ x < MOD := sorry

theorem solve_deterministic {N K : Nat} {A : List Nat}
  (h1 : N ≥ 2) (h2 : K ≥ 1) (h3 : A.length = N) :
  solve N K A = solve N K A := sorry

theorem solve_order_independent {N K : Nat} {A : List Nat}
  (h1 : N ≥ 2) (h2 : K ≥ 1) (h3 : A.length = N) :
  solve N K A = solve N K A.reverse := sorry

theorem solve_zeros {N K : Nat}
  (h1 : N ≥ 2) (h2 : K ≥ 1) :
  ∀ x ∈ solve N K (List.replicate N 0), x = 0 := sorry

theorem solve_ones_first_power {N K : Nat}
  (h1 : N ≥ 2) (h2 : K ≥ 1) :
  let num_pairs := (N * (N-1)) / 2;
  (solve N K (List.replicate N 1)).get! 0 = (num_pairs * 2) % MOD := sorry
-- </vc-theorems>