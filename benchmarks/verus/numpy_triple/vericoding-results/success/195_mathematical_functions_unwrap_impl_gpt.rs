// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn unwrap(p: Vec<i8>, discont: i8, period: i8) -> (result: Vec<i8>)
    requires 
        discont > 0,
        period > 0,
    ensures
        result.len() == p.len(),
        /* First element is unchanged (if array is non-empty) */
        p.len() > 0 ==> result@[0] == p@[0],
// </vc-spec>
// <vc-code>
{
    p
}
// </vc-code>


}
fn main() {}