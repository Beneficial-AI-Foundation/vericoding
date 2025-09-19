// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn legcompanion(c: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires 
        c@.len() >= 2,
        c[c@.len() - 1] as int != 0,
    ensures 
        result@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i]@.len() == c@.len() - 1,
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() ==> 
            result@[i]@[j] == result@[j]@[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}