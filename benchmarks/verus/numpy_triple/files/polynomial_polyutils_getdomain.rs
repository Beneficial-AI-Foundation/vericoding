// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn getdomain(x: Vec<i8>) -> (result: Vec<i8>)
    requires x@.len() > 0,
    ensures
        result@.len() == 2,
        result@[0] as int <= result@[1] as int,
        forall|i: int| 0 <= i < x@.len() ==> result@[0] as int <= x@[i] as int && x@[i] as int <= result@[1] as int,
        exists|i: int| 0 <= i < x@.len() && x@[i] as int == result@[0] as int,
        exists|j: int| 0 <= j < x@.len() && x@[j] as int == result@[1] as int,
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