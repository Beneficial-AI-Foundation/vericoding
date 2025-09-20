-- <vc-preamble>
structure SegTree where
  size : Nat
  answer : Array Nat
  opened : Array Nat
  closed : Array Nat
deriving Inhabited
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def next_pow_2 (n: Nat) : Nat :=
sorry

def SegTree.build (self : SegTree) (s : String) : SegTree :=
sorry

def solve_brackets (s: String) (queries: List (Nat × Nat)) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem next_pow_2_properties (n: Nat) (h: n ≥ 1) :
  let result := next_pow_2 n
  result ≥ n ∧
  result &&& (result - 1) = 0 ∧
  (result / 2 < n ∨ n = 1) :=
sorry

theorem segtree_build_properties (s : String) (h: s.length > 0) :
  let tree := SegTree.build (SegTree.mk s.length #[] #[] #[]) s
  tree.answer.size = 2 * tree.size ∧
  tree.opened.size = 2 * tree.size ∧
  tree.closed.size = 2 * tree.size ∧
  ∀ i < s.length,
    let idx := tree.size + i
    (tree.opened.get! idx = 0 ∨ tree.opened.get! idx = 1) ∧
    (tree.closed.get! idx = 0 ∨ tree.closed.get! idx = 1) ∧
    tree.opened.get! idx + tree.closed.get! idx ≤ 1 :=
sorry

theorem solve_brackets_properties (s: String) (queries: List (Nat × Nat))
  (h₁: s.length > 0)
  (h₂: ∀ q, q ∈ queries →
    q.1 > 0 ∧ q.2 > 0 ∧ q.1 ≤ q.2 ∧ q.2 ≤ s.length) :
  let results := solve_brackets s queries
  (∀ r, r ∈ results → r ≥ 0) ∧
  (∀ r, r ∈ results → r % 2 = 0) ∧
  (∀ q r, q ∈ queries → r ∈ results →
    r ≤ 2 * (q.2 - q.1 + 1) ∧
    (r > 0 → q.2 - q.1 ≥ 1)) :=
sorry
-- </vc-theorems>