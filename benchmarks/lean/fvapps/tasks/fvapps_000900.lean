-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_consecutive_jars (n k : Nat) (chocolates : List Nat) : Nat := sorry

theorem find_max_consecutive_jars_bounds (k n : Nat) (chocolates : List Nat)
    (h1 : 2 ≤ n) (h2 : n ≤ 100) (h3 : 1 ≤ k) (h4 : k ≤ 1000)
    (h5 : 2 ≤ chocolates.length) (h6 : chocolates.length ≤ 100)
    (h7 : ∀ x ∈ chocolates, 1 ≤ x ∧ x ≤ 1000) : 
    let result := find_max_consecutive_jars n k chocolates
    1 ≤ result ∧ result ≤ n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_consecutive_jars_valid_sequence (k n : Nat) (chocolates : List Nat)
    (h1 : 2 ≤ n) (h2 : n ≤ 100) (h3 : 1 ≤ k) (h4 : k ≤ 1000)
    (h5 : 2 ≤ chocolates.length) (h6 : chocolates.length ≤ 100)
    (h7 : ∀ x ∈ chocolates, 1 ≤ x ∧ x ≤ 1000) :
    let result := find_max_consecutive_jars n k chocolates
    ∃ i, i + result ≤ chocolates.length ∧
    let subseq := (chocolates.take (i + result)).drop i
    ∀ j, j + 1 < subseq.length →
    (List.get! subseq j + List.get! subseq (j+1)) ≤ k := sorry

theorem find_max_consecutive_jars_monotonic (k : Nat) (chocolates : List Nat)
    (h1 : 2 ≤ k) (h2 : k ≤ 100) 
    (h3 : 2 ≤ chocolates.length) (h4 : chocolates.length ≤ 100)
    (h5 : ∀ x ∈ chocolates, 1 ≤ x ∧ x ≤ 10) :
    let n := chocolates.length
    find_max_consecutive_jars n k chocolates ≤ 
    find_max_consecutive_jars n (2*k) chocolates := sorry

theorem find_max_consecutive_jars_sort_invariant (chocolates : List Nat)
    (h1 : 2 ≤ chocolates.length)
    (h2 : ∀ x ∈ chocolates, 1 ≤ x) :
    let n := chocolates.length
    let k := 2 * (List.foldl Nat.max 0 chocolates) 
    find_max_consecutive_jars n k chocolates =
    find_max_consecutive_jars n k chocolates := sorry
-- </vc-theorems>