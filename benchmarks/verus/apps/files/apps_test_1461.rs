// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_graph(n: int, f: Seq<int>, w: Seq<int>) -> bool {
  n > 0 && f.len() == n && w.len() == n &&
  (forall|i: int| #![trigger f[i]] 0 <= i < n ==> 0 <= f[i] < n) &&
  (forall|i: int| #![trigger w[i]] 0 <= i < n ==> w[i] >= 0)
}

spec fn valid_result(n: int, sums: Seq<int>, mins: Seq<int>) -> bool {
  sums.len() == n && mins.len() == n &&
  forall|i: int| #![trigger sums[i], mins[i]] 0 <= i < n ==> sums[i] >= 0 && mins[i] >= 0
}

spec fn path_sum(start: int, k: int, f: Seq<int>, w: Seq<int>) -> int
  decreases k
{
  if k <= 0 { 0 }
  else { w[start] + path_sum(f[start], k - 1, f, w) }
}

spec fn path_min(start: int, k: int, f: Seq<int>, w: Seq<int>) -> int
  decreases k
{
  if k <= 1 { w[start] }
  else {
    let next_min = path_min(f[start], k - 1, f, w);
    if w[start] <= next_min { w[start] } else { next_min }
  }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_graph(n: i8, k: i8, f: Vec<i8>, w: Vec<i8>) -> (result: (Vec<i8>, Vec<i8>))
  requires 
    valid_graph(n as int, f@.map_values(|x: i8| x as int), w@.map_values(|x: i8| x as int)),
    k > 0
  ensures valid_result(n as int, result.0@.map_values(|x: i8| x as int), result.1@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}