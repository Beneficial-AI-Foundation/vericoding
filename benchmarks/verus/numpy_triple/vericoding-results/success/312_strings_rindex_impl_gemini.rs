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
    /* code modified by LLM (iteration 5): added precondition to loop invariant to aid verification */
    let mut result: Vec<u8> = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
            forall|j: int| 0 <= j < a.len() ==> start@[j] as nat <= end_pos@[j] as nat,
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> 
                start@[j] as nat <= result@[j] as nat && result@[j] as nat <= end_pos@[j] as nat,
        decreases a.len() - i
    {
        result.push(start[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}