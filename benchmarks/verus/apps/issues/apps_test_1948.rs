// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, x: int, edges: Seq<(int, int)>) -> bool {
  n > 0 && 1 <= x <= n && edges.len() == n - 1 &&
  forall|e: (int, int)| #[trigger] edges.contains(e) ==> 0 <= e.0 < n && 0 <= e.1 < n
}

spec fn valid_distances(way_a: Seq<int>, way_b: Seq<int>, n: int, x: int) -> bool {
  way_a.len() == n && way_b.len() == n && n > 0 && 1 <= x <= n &&
  way_a[0] == 0 && way_b[x-1] == 0 &&
  forall|i: int| 0 <= i < n ==> #[trigger] way_a[i] >= 0 && #[trigger] way_b[i] >= 0
}

spec fn valid_leaves(leaves: Seq<int>, edges: Seq<(int, int)>, n: int) -> bool {
  valid_input(n, 1, edges) ==>
  (forall|i: int| 0 <= i < leaves.len() ==> 0 <= #[trigger] leaves[i] < n) &&
  (forall|i: int| 0 <= i < leaves.len() ==> is_leaf_node(#[trigger] leaves[i], edges, n)) &&
  (forall|i: int| 0 <= i < n ==> is_leaf_node(i, edges, n) ==> #[trigger] leaves.contains(i)) &&
  no_duplicates(leaves)
}

spec fn optimal_moves(way_a: Seq<int>, way_b: Seq<int>, leaves: Seq<int>, x: int) -> int {
  2 * compute_optimal_moves(way_a, way_b, leaves, x-1)
}
spec fn is_leaf_node(node: int, edges: Seq<(int, int)>, n: int) -> bool {
  if 0 <= node < n {
    let degree = edges.filter(|e: (int, int)| e.0 == node || e.1 == node).len();
    degree <= 1
  } else {
    false
  }
}

spec fn no_duplicates(s: Seq<int>) -> bool {
  forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j ==> #[trigger] s[i] != #[trigger] s[j]
}

spec fn compute_optimal_moves(way_a: Seq<int>, way_b: Seq<int>, leaves: Seq<int>, x: int) -> int {
  if leaves.len() == 0 {
    0
  } else {
    let max_leaf = leaves.fold_left(0, |acc: int, leaf: int| 
      if way_a[leaf] + way_b[leaf] > acc { way_a[leaf] + way_b[leaf] } else { acc }
    );
    max_leaf
  }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, x: i8, edges: Vec<(i8, i8)>, leaves: Vec<i8>, way_a: Vec<i8>, way_b: Vec<i8>) -> (result: i8)
  requires 
    valid_input(n as int, x as int, edges@.map(|e: (i8, i8)| (e.0 as int, e.1 as int))) &&
    valid_distances(way_a@.map(|w: i8| w as int), way_b@.map(|w: i8| w as int), n as int, x as int) &&
    valid_leaves(leaves@.map(|l: i8| l as int), edges@.map(|e: (i8, i8)| (e.0 as int, e.1 as int)), n as int) &&
    (forall|i: int| 0 <= i < leaves@.len() ==> 
      (0 <= leaves@[i] as int < way_a@.len()) && 
      (0 <= leaves@[i] as int < way_b@.len()))
  ensures 
    result >= 0 &&
    result as int == optimal_moves(way_a@.map(|w: i8| w as int), way_b@.map(|w: i8| w as int), leaves@.map(|l: i8| l as int), x as int) &&
    (result as int) % 2 == 0 &&
    result as int >= 2 * way_a@[(x-1) as int] as int
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}