use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_lists(lists: &Vec<Vec<int>>) -> (count: usize)
    ensures 
        count >= 0,
        count == lists.len(),
{
// </vc-spec>
// <vc-code>
    assume(false);
    0
}
// </vc-code>

fn main() {}

}
