// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn square_f64(x: f64) -> f64;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): retained noop helper to satisfy helper section */
spec fn helper_noop() -> bool { true }

// </vc-helpers>

// <vc-spec>
fn numpy_square(x: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == square_f64(x[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement numpy_square with correct int-based invariants */
    let n = x.len();
    let mut result: Vec<f64> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == square_f64(x[j]),
        decreases n - i
    {
        let xi: f64 = x[i];
        let sq: f64 = xi * xi;
        result.push(sq);
        i += 1;
    }

    result
}

// </vc-code>

}
fn main() {}