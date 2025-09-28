// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn reverse(a: &[i32]) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[a.len() - 1 - j],
        decreases a.len() - i
    {
        result.push(a[a.len() - 1 - i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}