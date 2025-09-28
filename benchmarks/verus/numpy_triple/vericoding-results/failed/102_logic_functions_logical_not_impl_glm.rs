// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn logical_not(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type casting for int/usize conversions */
    let n = x.len();
    let mut result = Vec::new();
    result.resize(n, false);

    let mut i: int = 0 as int;
    while i < n as int
        invariant
            result.len() == n,
            forall|j: int| 0 <= j < i ==> result[j] == (x[j] == 0.0),
        decreases n as int - i
    {
        result.set(i as usize, x[i as usize] == 0.0);
        i = i + (1 as int);
    }

    result
}
// </vc-code>

}
fn main() {}