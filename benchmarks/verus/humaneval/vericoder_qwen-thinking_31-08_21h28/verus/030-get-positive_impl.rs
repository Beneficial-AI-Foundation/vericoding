use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_positive(x: i32) -> bool
    ensures
        is_positive(x) == (x > 0)
{
    x > 0
}
// </vc-helpers>

// <vc-spec>
fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)
    // post-conditions-start
    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    Seq::to_vec(input@.filter(|x: i32| x > 0))
}
// </vc-code>

fn main() {}
}