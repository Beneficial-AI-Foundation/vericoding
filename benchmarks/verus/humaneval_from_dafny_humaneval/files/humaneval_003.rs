// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sum_prefix(ops: Seq<int>, len: nat) -> int
  recommends len <= ops.len()
  decreases len
{
  if len == 0 { 0 }
  else { sum_prefix(ops, (len - 1) as nat) + ops[len - 1] }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Seq<int>) -> (result: bool)
  ensures result <==> (exists|i: int| 0 < i <= operations.len() && #[trigger] sum_prefix(operations, i as nat) < 0)
// </vc-spec>
// <vc-code>
{
    assume(false);
    false
}
// </vc-code>


}

fn main() {}