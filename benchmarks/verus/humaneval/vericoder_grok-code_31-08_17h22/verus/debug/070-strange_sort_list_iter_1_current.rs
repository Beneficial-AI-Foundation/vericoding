use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn strange_sort_list(s: &Vec<i32>) -> (ret: Vec<i32>)
    // post-conditions-start
    ensures
        s@.len() == ret@.len(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    s.clone()
    // impl-end
}
// </vc-code>

fn main() {}
}