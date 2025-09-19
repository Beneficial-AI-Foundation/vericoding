// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_odd(x: i32) -> bool {
    x % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_first_odd(a: &Vec<i8>) -> (result: Option<usize>)
    requires a.len() > 0,
    ensures
        match result {
            Some(idx) => idx < a.len() && is_odd(a[idx as int] as i32) &&
                forall|j: int| 0 <= j < idx ==> !is_odd(a[j] as i32),
            None => forall|i: int| 0 <= i < a@.len() ==> !is_odd(a[i] as i32),
        },
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}