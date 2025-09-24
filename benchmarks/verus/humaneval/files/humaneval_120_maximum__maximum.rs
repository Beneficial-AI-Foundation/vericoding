// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn maximum(s: Vec<i8>, k: i8) -> (result: Vec<i8>)
  requires 
      1 <= k as int <= s@.len(),
      1 <= s@.len() <= 1000,
      forall|x: i8| s@.contains(x) ==> -1000 <= x as int <= 1000,
  ensures 
      result@.len() == k as int,
      forall|i: int, j: int| 0 <= i < j < k as int ==> result@[i] as int <= result@[j] as int,
      forall|x: i8| result@.contains(x) ==> s@.contains(x),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}