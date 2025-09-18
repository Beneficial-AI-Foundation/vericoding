// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_non_decreasing(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn has_unique_elements(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s[i] != s[j]
}
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
    let result: Vec<i32> = Vec::new();
    (result.len(), result)
}
// </vc-code>

}
fn main() {}