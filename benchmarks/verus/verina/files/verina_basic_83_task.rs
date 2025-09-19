// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn concat(a: &Vec<i8>, b: &Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len() + b.len(),
        forall|k: int| 0 <= k < a.len() ==> result[k] as i8 == a[k],
        forall|k: int| 0 <= k < b.len() ==> result[k + a.len()] as i8 == b[k],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}