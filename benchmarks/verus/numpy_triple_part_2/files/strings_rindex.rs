// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn rindex(a: Vec<String>, sub: Vec<String>, start: Vec<usize>, end_pos: Vec<usize>) -> (result: Vec<usize>)
    requires 
        a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            start[i] <= end_pos[i] &&
            end_pos[i] <= 1000 &&
            start[i] <= end_pos[i]
        },
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            start[i] <= result[i] && 
            result[i] <= end_pos[i]
        }
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