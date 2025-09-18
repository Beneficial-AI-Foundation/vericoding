// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn helper_empty() -> bool { true }
// </vc-helpers>

// <vc-spec>
fn unique(ar: Vec<i32>) -> (result: (usize, Vec<i32>))
    ensures
        result.1.len() <= ar.len(),

        forall|i: int, j: int| 0 <= i < j < result.1.len() ==> result.1[i as int] <= result.1[j as int],

        forall|i: int, j: int| 0 <= i < result.1.len() && 0 <= j < result.1.len() && i != j ==> result.1[i as int] != result.1[j as int],
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<i32> = Vec::new();
    (res.len(), res)
}
// </vc-code>

}
fn main() {}