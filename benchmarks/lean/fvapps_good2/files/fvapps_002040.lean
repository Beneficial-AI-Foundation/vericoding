-- <vc-preamble>
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_valid_permutations (n : Nat) (edges : List (Nat × Nat)) : Nat :=
sorry

def is_valid_tree (n : Nat) (edges : List (Nat × Nat)) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_tree_construction (n : Nat) (edges : List (Nat × Nat))
  (h1 : is_valid_tree n edges) :
  let result := count_valid_permutations n edges
  ∃ (k : Nat), result = k ∧
    k > 0 ∧
    k ≤ n * factorial n :=
sorry

theorem mod_result (n : Nat) (edges : List (Nat × Nat)) :
  let result := count_valid_permutations n edges
  result < 998244353 :=
sorry
-- </vc-theorems>