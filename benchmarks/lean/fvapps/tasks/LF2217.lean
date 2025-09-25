-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 998244353

def solve (n k : Nat) (a b : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_bounds {n k : Nat} {a b : List Nat}
    (h1 : n > 0)
    (h2 : k > 0)
    (h3 : k ≤ n)
    (h4 : k ≤ 100)
    (h5 : n ≤ 100) 
    (h6 : a.length = n)
    (h7 : b.length = k)
    (h8 : ∀ x ∈ a, 1 ≤ x ∧ x ≤ n)
    (h9 : ∀ x ∈ b, 1 ≤ x ∧ x ≤ n) :
    let result := solve n k a b
    0 ≤ result ∧ result < MOD :=
  sorry

theorem solve_minimal_case {n : Nat} {a b : List Nat}
    (h1 : n > 0)
    (h2 : n ≤ 5)
    (h3 : a.length = n)
    (h4 : b.length = 1)
    (h5 : ∀ x ∈ a, 1 ≤ x ∧ x ≤ n)
    (h6 : ∀ x ∈ b, 1 ≤ x ∧ x ≤ n) :
    let result := solve n 1 a b
    result = 0 ∨ result = 1 ∨ result = 2 :=
  sorry

theorem solve_edge_case_one {a b : List Nat}
    (h1 : a.length = 1)
    (h2 : b.length = 1)
    (h3 : ∀ x ∈ a, x = 1)
    (h4 : ∀ x ∈ b, x = 1) :
    let result := solve 1 1 a b
    0 ≤ result ∧ result < MOD :=
  sorry

theorem solve_edge_case_two_one {a b : List Nat}
    (h1 : a.length = 2)
    (h2 : b.length = 1)
    (h3 : ∀ x ∈ a, 1 ≤ x ∧ x ≤ 2)
    (h4 : ∀ x ∈ b, 1 ≤ x ∧ x ≤ 2) :
    let result := solve 2 1 a b
    0 ≤ result ∧ result < MOD :=
  sorry

theorem solve_edge_case_two_two {a b : List Nat}
    (h1 : a.length = 2)
    (h2 : b.length = 2)
    (h3 : ∀ x ∈ a, 1 ≤ x ∧ x ≤ 2)
    (h4 : ∀ x ∈ b, 1 ≤ x ∧ x ≤ 2) :
    let result := solve 2 2 a b
    0 ≤ result ∧ result < MOD :=
  sorry
-- </vc-theorems>