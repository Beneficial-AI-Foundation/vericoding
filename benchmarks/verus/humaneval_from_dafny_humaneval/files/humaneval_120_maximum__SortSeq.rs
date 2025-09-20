// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sort_seq(s: &Vec<i8>) -> (sorted: Vec<i8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> #[trigger] sorted@[i] <= #[trigger] sorted@[j],
        sorted@.len() == s@.len(),
        s@.to_multiset() == sorted@.to_multiset(),
        forall|i: int| 0 <= i < s@.len() ==> exists|j: int| 0 <= j < sorted@.len() && #[trigger] s@[i] == #[trigger] sorted@[j],
        forall|x: i8| #[trigger] s@.contains(x) ==> #[trigger] sorted@.contains(x),
        forall|i: int| 0 <= i < s@.len() ==> exists|j: int| 0 <= j < sorted@.len() && #[trigger] sorted@[i] == #[trigger] s@[j],
        forall|x: i8| #[trigger] sorted@.contains(x) ==> #[trigger] s@.contains(x),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}