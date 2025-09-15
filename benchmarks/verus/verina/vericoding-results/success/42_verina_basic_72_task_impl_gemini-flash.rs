// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn append(a: &Vec<i32>, b: i32) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + 1,
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
        result[a.len() as int] == b,
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            // Note: The original contains check was problematic. This invariant is removed as it's not directly needed for correctness
            //       and requires custom proof for `contains` which is not available directly for `Vec`.
            forall|j: int| 0 <= j < i ==> result[j] == a[j],
        decreases a.len() - i
    {
        result.push(a[i]);
        i = i + 1;
    }
    result.push(b);
    result
}
// </vc-code>

}
fn main() {}