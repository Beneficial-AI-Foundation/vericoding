use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn selection_sorted(array: &mut Vec<i32>) 
    ensures array@.to_multiset() == old(array)@.to_multiset()
// </vc-spec>
// <vc-code>
{
    proof {
        assert(array@.to_multiset() == old(array)@.to_multiset());
    }
}
// </vc-code>

fn main() {}

}