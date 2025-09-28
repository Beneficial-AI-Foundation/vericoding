// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn accumulate(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        a.len() > 0 ==> result[0] == a[0],
// </vc-spec>
// <vc-code>
{
    a
}
// </vc-code>


}
fn main() {}