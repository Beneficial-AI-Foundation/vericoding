-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_optimal_split (N k : Nat) (powers : List Nat) : Nat :=
sorry

def calc_product (values : List Nat) (split : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_optimal_split_properties1 {N k : Nat} {powers : List Nat} (h1: N ≥ 2) (h2: k ≥ 1)
    (h3: powers.length = N) (h4: ∀ x ∈ powers, x ≤ 10) :
    let result := find_optimal_split N k powers
    1 ≤ result ∧ result ≤ N-1 :=
sorry

theorem find_optimal_split_properties2 {N k : Nat} {powers : List Nat} (h1: N ≥ 2) (h2: k ≥ 1)
    (h3: powers.length = N) (h4: ∀ x ∈ powers, x ≤ 10) :
    let values := powers.map (fun p => k^p)
    let result := find_optimal_split N k powers
    let optimal_product := calc_product values result
    ∀ i, 1 ≤ i → i < N → calc_product values i ≤ optimal_product :=
sorry
-- </vc-theorems>