-- <vc-preamble>
def find_nodes_with_distance (t : Tree) (node : Nat) (dist : Nat) : List Nat :=
  sorry

def resolve_query (t : Tree) (a b c d : Nat) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def resolve_queries (t : Tree) (qs : List (Nat × Nat × Nat × Nat)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem queries_results_length_matches {t : Tree} {qs : List (Nat × Nat × Nat × Nat)} :
  let results := resolve_queries t qs
  List.length results = List.length qs := sorry

theorem results_are_valid_nodes_or_neg_one {t : Tree} {qs : List (Nat × Nat × Nat × Nat)} :
  let results := resolve_queries t qs
  ∀ r ∈ results, r = -1 ∨ (1 ≤ Int.toNat r ∧ Int.toNat r ≤ t.n) := sorry

theorem zero_distance_to_self {t : Tree} {node : Nat} :
  node ≤ t.n →
  find_nodes_with_distance t node 0 = [node] := sorry

theorem zero_distance_query {t : Tree} {a b : Nat} :
  a ≤ t.n →
  b ≤ t.n →
  resolve_query t a 0 b 0 = if a = b then Int.ofNat a else -1 := sorry

theorem nodes_at_distance_unique {t : Tree} {node dist : Nat} :
  node ≤ t.n →
  let nodes := find_nodes_with_distance t node dist
  List.Nodup nodes := sorry

theorem nodes_at_distance_valid {t : Tree} {node dist : Nat} :
  node ≤ t.n →
  let nodes := find_nodes_with_distance t node dist
  ∀ n ∈ nodes, 1 ≤ n ∧ n ≤ t.n := sorry
-- </vc-theorems>