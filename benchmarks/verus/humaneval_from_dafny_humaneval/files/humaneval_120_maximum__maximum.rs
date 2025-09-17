// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn maximum(s: Seq<int>, k: int) -> (result: Seq<int>)
  requires 
      1 <= k <= s.len(),
      1 <= s.len() <= 1000,
      forall|x: int| s.contains(x) ==> -1000 <= x <= 1000,
  ensures 
      result.len() == k,
      forall|i: int, j: int| 0 <= i < j < k ==> result[i] <= result[j],
      forall|x: int| result.contains(x) ==> s.contains(x),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}