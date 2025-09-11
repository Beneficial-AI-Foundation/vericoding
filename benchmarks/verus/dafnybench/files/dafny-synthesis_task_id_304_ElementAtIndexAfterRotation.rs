// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn element_at_index_after_rotation(l: Seq<int>, n: int, index: int) -> (element: int)
    requires 
        n >= 0,
        0 <= index < l.len(),
    ensures 
        element == l[((index - n + l.len() as int) % l.len() as int) as int],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}