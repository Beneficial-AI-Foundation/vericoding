// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_of_list(lst: Vec<i32>) -> (result: i32)
    requires lst.len() > 0,
    ensures
        exists|i: int| 0 <= i < lst.len() && lst[i] == result,
        forall|i: int| 0 <= i < lst.len() ==> lst[i] <= result,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}