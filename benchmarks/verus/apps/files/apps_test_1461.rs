// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_graph(n: int, f: Seq<int>, w: Seq<int>) -> bool {
  n > 0 && f.len() == n && w.len() == n &&
  (forall|i: int| 0 <= i < n ==> 0 <= f[i] < n) &&
  (forall|i: int| 0 <= i < n ==> w[i] >= 0)
}

spec fn valid_result(n: int, sums: Seq<int>, mins: Seq<int>) -> bool {
  sums.len() == n && mins.len() == n &&
  forall|i: int| 0 <= i < n ==> sums[i] >= 0 && mins[i] >= 0
}

spec fn path_sum(start: int, k: int, f: Seq<int>, w: Seq<int>) -> int
  requires 
    f.len() == w.len() && f.len() > 0,
    0 <= start < f.len(),
    k >= 0,
    forall|i: int| 0 <= i < f.len() ==> 0 <= f[i] < f.len(),
    forall|i: int| 0 <= i < w.len() ==> w[i] >= 0,
  decreases k
{
  if k == 0 {
    0
  } else {
    w[start] + path_sum(f[start], k - 1, f, w)
  }
}

spec fn path_min(start: int, k: int, f: Seq<int>, w: Seq<int>) -> int
  requires 
    f.len() == w.len() && f.len() > 0,
    0 <= start < f.len(),
    k > 0,
    forall|i: int| 0 <= i < f.len() ==> 0 <= f[i] < f.len(),
    forall|i: int| 0 <= i < w.len() ==> w[i] >= 0,
  decreases k
{
  if k == 1 {
    w[start]
  } else {
    let next_min = path_min(f[start], k - 1, f, w);
    if w[start] <= next_min { w[start] } else { next_min }
  }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_graph(n: int, k: int, f: Seq<int>, w: Seq<int>) -> (result: (Seq<int>, Seq<int>))
  requires 
    valid_graph(n, f, w),
    k > 0,
  ensures valid_result(n, result.0, result.1)
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}