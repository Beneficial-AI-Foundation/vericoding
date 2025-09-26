// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn rindex(a: Vec<String>, sub: Vec<String>, start: Vec<u8>, end_pos: Vec<u8>) -> (result: Vec<u8>)
    requires 
        a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            start[i] as nat <= end_pos[i] as nat &&
            end_pos[i] as nat <= 1000 &&
            start[i] as nat <= end_pos[i] as nat
        },
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            start[i] as nat <= result[i] as nat && 
            result[i] as nat <= end_pos[i] as nat
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