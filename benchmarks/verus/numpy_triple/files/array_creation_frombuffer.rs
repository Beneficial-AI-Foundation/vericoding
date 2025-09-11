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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}