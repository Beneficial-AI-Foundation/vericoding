// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn arccos(x: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> -1 <= x[i] as int && x[i] as int <= 1,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> (
            0 <= result[i] as int && 
            result[i] as int <= 3 &&
            (x[i] as int == -1 ==> result[i] as int == 3) &&
            (x[i] as int == 1 ==> result[i] as int == 0)
        ),
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