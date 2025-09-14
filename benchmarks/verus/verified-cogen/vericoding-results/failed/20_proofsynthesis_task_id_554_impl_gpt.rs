// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_odd(x: u32) -> bool { x % 2 != 0 }
// </vc-helpers>

// <vc-spec>
fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)

    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
// </vc-spec>
// <vc-code>
{
    let ghost s: Seq<u32> = arr@.filter(|x: u32| x % 2 != 0);
    let result = Vec::<u32>::from_seq(s);
    result
}
// </vc-code>

}
fn main() {}