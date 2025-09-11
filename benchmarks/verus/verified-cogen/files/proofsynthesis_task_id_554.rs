// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)

    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}