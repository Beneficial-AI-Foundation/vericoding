// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn to_array(xs: &Seq<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i],
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < xs.len()
        invariant i <= xs.len(),
        invariant result.len() == i,
        invariant forall|j: int| 0 <= j < i ==> result[j] == xs[j]
    {
        result.push(xs[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}