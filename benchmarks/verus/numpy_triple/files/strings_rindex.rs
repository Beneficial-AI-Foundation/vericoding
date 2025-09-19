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
            start[i] as int <= end_pos[i] as int &&
            end_pos[i] as int <= 1000 &&
            start[i] as int <= end_pos[i] as int
        },
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            start[i] as int <= result[i] as int && 
            result[i] as int <= end_pos[i] as int
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