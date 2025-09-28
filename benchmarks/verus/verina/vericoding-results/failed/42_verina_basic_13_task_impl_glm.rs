// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn cube_spec_helper(a: &Vec<i32>, i: int) -> int
    requires
        0 <= i < a.len(),
    ensures
        cube_spec_helper(a, i) == a[i] * a[i] * a[i],
{
    a[i] * a[i] * a[i]
}
// </vc-helpers>

// <vc-spec>
fn cube_elements(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * a[i] * a[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] * a[j] * a[j],
        decreases a.len() - i
    {
        result.push(a[i] * a[i] * a[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}