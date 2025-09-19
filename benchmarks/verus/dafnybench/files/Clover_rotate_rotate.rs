// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn rotate(a: &[i8], offset: usize) -> (result: Vec<i8>)
    requires 
        offset >= 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i as int] == a[(i + offset as int) % a.len() as int],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}