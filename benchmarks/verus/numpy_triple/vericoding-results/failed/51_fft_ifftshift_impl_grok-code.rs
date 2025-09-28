// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes */
// </vc-helpers>

// <vc-spec>
fn ifftshift(x: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> 
            result[i] == x[((i + (x@.len() as int) / 2) % (x@.len() as int)) as int]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): adjusting invariant quantifier to use nat for indices and casting to avoid type issues */
    let len: usize = x.len();
    let shift: usize = len / 2;
    let mut result: Vec<f32> = Vec::with_capacity(len);
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result@.len() == i,
            forall|j: nat| j < i ==> result@[(j as int)] == x@[((j as int + (len as int) / 2) % (len as int)) as int],
        decreases len - i
    {
        let shifted_i: usize = i.wrapping_add(shift);
        let src_index: usize = if shifted_i >= len { shifted_i.wrapping_sub(len) } else { shifted_i };
        result.push(x[src_index]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}