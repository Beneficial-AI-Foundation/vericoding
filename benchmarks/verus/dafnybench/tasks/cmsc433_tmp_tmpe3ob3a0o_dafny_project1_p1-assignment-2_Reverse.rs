// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn reverse(a: &Vec<i32>) -> (a_rev: Vec<i32>)
    ensures
        a_rev.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] == a_rev[a_rev.len() - i - 1]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}