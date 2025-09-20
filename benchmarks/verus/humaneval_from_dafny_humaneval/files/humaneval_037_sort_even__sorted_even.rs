// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sorted_even(a: Vec<i8>) -> (sorted: Vec<i8>)
    requires 
        a@.len() > 0
    ensures 
        sorted@.len() == a@.len(),
        forall|i: int, j: int| 0 <= i < j && 2 * i < sorted@.len() && 2 * j < sorted@.len() ==> #[trigger] sorted@[2 * i] <= #[trigger] sorted@[2 * j],
        forall|i: int| 0 <= i < a@.len() && i % 2 == 1 ==> #[trigger] sorted@[i] == #[trigger] a@[i],
        a@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}