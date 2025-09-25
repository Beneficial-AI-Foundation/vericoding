// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &[int]) -> (odd_list: Vec<int>)
    ensures 

        forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list[i]) && arr@.contains(odd_list[i]),

        forall|i: int| 0 <= i < arr.len() && is_odd(arr[i]) ==> odd_list@.contains(arr[i]),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}