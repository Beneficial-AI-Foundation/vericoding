// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn strictly_increasing(s: Seq<i32>) -> bool { forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] < s[j] }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique_better(a: &[i32]) -> (result: Vec<i32>)
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
// </vc-spec>
// <vc-code>
{
    Vec::new()
}
// </vc-code>

}
fn main() {}