use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn count_lists(lists: &Vec<Vec<int>>) -> (count: usize)
    ensures 
        count >= 0,
        count == lists.len(),
{
// </vc-spec>
// </vc-spec>

// <vc-code>
fn count_lists(lists: &Vec<Vec<int>>) -> (count: usize)
    ensures 
        count >= 0,
        count == lists.len(),
{
    lists.len()
}
// </vc-code>

fn main() {}

}