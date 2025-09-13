// <vc-preamble>
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, a: Seq<int>) -> bool {
  n >= 2 && a.len() == n
}

spec fn count_violations_for_k(a: Seq<int>, n: int, k: int) -> int {
  if n >= 2 && a.len() == n && 1 <= k <= n - 1 {
    set_int_range(2, n + 1).filter(|i: int| {
      let parent_idx = (i + k - 2) / k;
      parent_idx >= 1 && a[i-1] < a[parent_idx-1]
    }).len() as int
  } else {
    0
  }
}

spec fn valid_output(result: Seq<int>, n: int, a: Seq<int>) -> bool {
  if n >= 2 && a.len() == n {
    result.len() == n - 1 &&
    (forall|k: int| 1 <= k <= n - 1 ==> result[k-1] >= 0) &&
    (forall|k: int| 1 <= k <= n - 1 ==> result[k-1] == count_violations_for_k(a, n, k))
  } else {
    false
  }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, a: Seq<int>) -> (result: Seq<int>)
  requires valid_input(n, a)
  ensures valid_output(result, n, a)
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}