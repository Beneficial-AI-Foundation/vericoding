// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn split_and_append(l: Vec<i8>, n: i8) -> (r: Vec<i8>)
    requires 
        n >= 0 && (n as int) < l@.len(),
    ensures 
        r@.len() == l@.len(),
        forall|i: int| 0 <= i < l@.len() ==> r@[i] == l@[((i + (n as int)) as nat % l@.len()) as int],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}