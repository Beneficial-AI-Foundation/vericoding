// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermemulx(c: Vec<f64>) -> (result: Vec<f64>)
    requires c.len() >= 0,
    ensures
        result.len() == c.len() + 1,
        result[0] == 0.0,
        forall|i: int| 1 <= i < c.len() ==> result[i + 1] == c[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    result.push(0.0);
    let mut i = 0;
    while i < c.len()
        invariant
            i <= c.len(),
            result.len() == i + 1,
            result[0] == 0.0,
            forall|j: int| 1 <= j && j <= i ==> result[j] == c[j - 1],
        decreases c.len() - i,
    {
        result.push(c[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}