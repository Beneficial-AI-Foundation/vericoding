// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_odd(x: i32) -> bool {
    x % 2 != 0
}
// </vc-helpers>

// <vc-spec>
fn find_first_odd(a: &Vec<i32>) -> (result: Option<usize>)
    requires a.len() > 0,
    ensures
        match result {
            Some(idx) => idx < a.len() && is_odd(a[idx as int]) &&
                forall|j: int| 0 <= j < idx ==> !is_odd(a[j]),
            None => forall|i: int| 0 <= i < a.len() ==> !is_odd(a[i]),
        },
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    None
    // impl-end
}
// </vc-code>


}
fn main() {}