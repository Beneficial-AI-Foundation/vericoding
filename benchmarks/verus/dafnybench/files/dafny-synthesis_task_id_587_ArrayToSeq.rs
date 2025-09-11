// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn array_to_seq(a: &[i32]) -> (s: Vec<i32>)
    ensures
        s.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> s[i] == a[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}