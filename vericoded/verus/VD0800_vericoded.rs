// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count_lists(lists: &Vec<Vec<int>>) -> (count: usize)
    ensures 
        count >= 0,
        count == lists.len(),
// </vc-spec>
// <vc-code>
{
    lists.len()
}
// </vc-code>

}
fn main() {}