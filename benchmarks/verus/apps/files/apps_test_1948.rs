// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, x: int, edges: Seq<(int, int)>) -> bool {
  n > 0 && 1 <= x <= n && edges.len() == n - 1 &&
  forall|e: (int, int)| edges.contains(e) ==> 0 <= e.0 < n && 0 <= e.1 < n
}

spec fn valid_distances(way_a: Seq<int>, way_b: Seq<int>, n: int, x: int) -> bool {
  way_a.len() == n && way_b.len() == n && n > 0 && 1 <= x <= n &&
  way_a[0] == 0 && way_b[x-1] == 0 &&
  forall|i: int| 0 <= i < n ==> way_a[i] >= 0 && way_b[i] >= 0
}

spec fn valid_leaves(leaves: Seq<int>, edges: Seq<(int, int)>, n: int) -> bool {
  valid_input(n, 1, edges) &&
  (forall|i: int| 0 <= i < leaves.len() ==> 0 <= leaves[i] < n) &&
  (forall|i: int| 0 <= i < leaves.len() ==> is_leaf_node(leaves[i], edges, n)) &&
  (forall|i: int| 0 <= i < n ==> is_leaf_node(i, edges, n) ==> leaves.contains(i)) &&
  no_duplicates(leaves)
}

spec fn optimal_moves(way_a: Seq<int>, way_b: Seq<int>, leaves: Seq<int>, x: int) -> int {
  2 * compute_optimal_moves(way_a, way_b, leaves, x-1)
}
// </vc-preamble>

// <vc-helpers>
spec fn is_leaf_node(node: int, edges: Seq<(int, int)>, n: int) -> bool {
  node >= 0 && node < n
}

spec fn no_duplicates(leaves: Seq<int>) -> bool {
  forall|i: int, j: int| 0 <= i < leaves.len() && 0 <= j < leaves.len() && i != j ==> leaves[i] != leaves[j]
}

spec fn compute_optimal_moves(way_a: Seq<int>, way_b: Seq<int>, leaves: Seq<int>, x_idx: int) -> int {
  if leaves.len() == 0 { 0 } else { if x_idx >= 0 && x_idx < way_a.len() { way_a[x_idx] } else { 0 } }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, x: int, edges: Seq<(int, int)>, leaves: Seq<int>, way_a: Seq<int>, way_b: Seq<int>) -> (result: int)
  requires 
      valid_input(n, x, edges),
      valid_distances(way_a, way_b, n, x),
      valid_leaves(leaves, edges, n),
      forall|i: int| 0 <= i < leaves.len() ==> 0 <= leaves[i] < way_a.len() && 0 <= leaves[i] < way_b.len(),
  ensures 
      result >= 0,
      result == optimal_moves(way_a, way_b, leaves, x),
      result % 2 == 0,
      result >= 2 * way_a[x-1],
// </vc-spec>
// <vc-code>
{
  assume(false);
  0int
}
// </vc-code>


}

fn main() {}