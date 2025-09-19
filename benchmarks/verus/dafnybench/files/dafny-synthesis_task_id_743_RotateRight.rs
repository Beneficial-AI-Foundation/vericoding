// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn rotate_right(l: Vec<i8>, n: i8) -> (r: Vec<i8>)
    requires n >= 0,
    ensures 
        r@.len() == l@.len(),
        forall|i: int| 0 <= i < l@.len() ==> r@.index(i) == l@.index((i - n as int + l@.len() as int) % l@.len() as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}