// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn frombuffer(buffer: &Vec<u8>, count: usize, offset: usize) -> (result: Vec<u8>)
    requires 
        offset + count <= buffer.len(),
        offset < buffer.len() || count == 0,
    ensures
        result.len() == count,
        forall|i: int| 0 <= i < count ==> result[i] == buffer[offset + i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added invariant and proof block for bounds check */
    let mut result = Vec::with_capacity(count);
    let mut i: usize = 0;
    while i < count
        invariant
            i <= count,
            offset + count <= buffer.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == buffer@[offset as int + j],
        decreases count - i
    {
        assert(offset + i < buffer.len()) by {
            assert(i < count);
            assert(offset + count <= buffer.len());
        };
        result.push(buffer[offset + i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}