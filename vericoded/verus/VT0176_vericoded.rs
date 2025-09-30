// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_flatiter(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    a
}
// </vc-code>

}
fn main() {}