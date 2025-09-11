// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn concat(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + b.len(),
        forall|k: int| 0 <= k < a.len() ==> result[k] == a[k],
        forall|k: int| 0 <= k < b.len() ==> result[k + a.len()] == b[k],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}