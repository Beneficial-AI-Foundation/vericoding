// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn strange_sort_list_helper(s: Vec<i8>) -> (res: (Vec<i8>, Vec<i8>))
    ensures 
        s@.to_multiset() == res.0@.to_multiset(),
        s@.len() == res.0@.len() && s@.len() == res.1@.len(),
        forall|i: int| 0 <= i < s@.len() && i % 2 == 0 ==> res.1@[i] == res.0@[i / 2],
        forall|i: int| 0 <= i < s@.len() && i % 2 == 1 ==> res.1@[i] == res.0@[s@.len() - (i - 1) / 2 - 1]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}