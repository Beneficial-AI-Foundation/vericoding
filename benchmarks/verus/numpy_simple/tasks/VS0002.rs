// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn arange_length(start: int, stop: int, step: int) -> nat
{
    if step != 0 {
        if step < 0 {
            if start > stop {
                ((start - stop) / (-step)) as nat
            } else {
                0
            }
        } else {
            if start < stop {
                ((stop - start) / step) as nat
            } else {
                0
            }
        }
    } else {
        0
    }
}

fn arange(start: i8, stop: i8, step: i8) -> (result: Vec<i8>)
    requires 
        step != 0,
        if step < 0 { start > stop } else { start < stop },
    ensures
        result@.len() == arange_length(start as int, stop as int, step as int),
        result@.len() > 0,
        result@[0] == start as int
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}