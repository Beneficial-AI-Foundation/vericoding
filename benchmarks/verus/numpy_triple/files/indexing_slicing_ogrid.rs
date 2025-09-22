// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn ogrid(start: i8, stop: i8, step: i8, n: usize) -> (result: Vec<i8>)
    requires 
        step != 0,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result@[i] == start as int + i * (step as int),
        forall|i: int| 0 <= i < n ==> 
            if step > 0 { 
                (start as int) <= result@[i] && result@[i] < (stop as int)
            } else {
                (stop as int) < result@[i] && result@[i] <= (start as int)
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