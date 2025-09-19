// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn histogram2d(x: &Vec<i8>, y: &Vec<i8>, bins: u8) -> (result: (Vec<Vec<u8>>, Vec<i8>, Vec<i8>))
    requires 
        x@.len() == y@.len(),
        bins > 0,
    ensures
        result.0@.len() == bins as nat,
        forall|i: int| 0 <= i < bins as int ==> result.0@[i]@.len() == bins as nat,
        result.1@.len() == bins as nat + 1,
        result.2@.len() == bins as nat + 1,
        forall|i: int, j: int| 0 <= i < bins as int && 0 <= j < bins as int ==> result.0@[i]@[j] as nat <= x@.len(),
        forall|i: int| 0 <= i < bins as int ==> #[trigger] result.1@[i] as int <= result.1@[i + 1] as int,
        forall|i: int| 0 <= i < bins as int ==> #[trigger] result.2@[i] as int <= result.2@[i + 1] as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}