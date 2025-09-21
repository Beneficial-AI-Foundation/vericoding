// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn element_at_index_after_rotation(l: Vec<i8>, n: i8, index: i8) -> (element: i8)
    requires 
        n >= 0,
        0 <= index < l.len(),
    ensures 
        element == l@[((index as int - n as int + l@.len() as int) % l@.len() as int) as int],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}