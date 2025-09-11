// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn remove_odd_numbers(arr: &[i32]) -> (even_list: Vec<i32>)
    ensures

        forall|i: int| 0 <= i < even_list.len() ==> is_even(even_list[i] as int) && arr@.contains(even_list[i]),

        forall|i: int| 0 <= i < arr.len() && is_even(arr[i] as int) ==> even_list@.contains(arr[i])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}