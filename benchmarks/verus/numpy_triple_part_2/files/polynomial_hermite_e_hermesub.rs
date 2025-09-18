// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn hermesub(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i] as int == 
            (if i < c1.len() { c1[i] as int } else { 0 }) - 
            (if i < c2.len() { c2[i] as int } else { 0 })
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