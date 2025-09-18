// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn ogrid(start: i32, stop: i32, step: i32, n: usize) -> (result: Vec<i32>)
    requires 
        step != 0,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == start + (i as i32) * step,
        forall|i: int| 0 <= i < n ==> 
            if step > 0 { 
                start <= result[i] && result[i] < stop
            } else {
                stop < result[i] && result[i] <= start
            },
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