// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)

    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}