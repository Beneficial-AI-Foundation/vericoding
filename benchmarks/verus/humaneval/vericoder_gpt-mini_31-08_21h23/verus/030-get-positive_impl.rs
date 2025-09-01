use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_pos(x: i32) -> bool { x > 0 }

fn vec_of_positive(s: Seq<i32>) -> (v: Vec<i32>)
    ensures
        v@ == s.filter(|x: i32| x > 0)
{
    Vec::from_seq(s.filter(|x: i32| x > 0))
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
    vec_of_positive(input@)
}
// </vc-code>

fn main() {}
}