-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_interesting_subsequences (n k : Nat) (a : List Nat) : Nat :=
  sorry

def isSorted (l : List Nat) : Bool :=
  sorry

def sortList (l : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_interesting_subsequences_properties (n k : Nat) (a : List Nat)
    (h1 : n > 0) (h2 : k > 0) (h3 : List.length a > 0) :
    k ≤ List.length a →
    0 ≤ count_interesting_subsequences n k a :=
sorry

theorem sorted_input_equivalence (a : List Nat)
    (h1 : List.length a ≥ 2) :
    let k := List.length a / 2
    count_interesting_subsequences (List.length a) k (sortList a) =
    count_interesting_subsequences (List.length a) k a :=
sorry

theorem kth_element_boundary (a : List Nat)
    (h1 : List.length a ≥ 2) (h2 : List.length a ≤ 10) :
    let k := List.length a / 2
    let sorted := sortList a
    k > 0 →
    k ≤ List.length a →
    ∃ x, List.elem x a ∧ x = List.get! sorted (k-1) :=
sorry
-- </vc-theorems>