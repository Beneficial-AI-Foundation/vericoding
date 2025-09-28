// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): accept int index and prove non-zeroness using spec forall */
fn nonzero_index(x2: &Vec<f64>, j: int)
    requires
        forall|i: int| 0 <= i < x2.len() ==> x2@[i] != 0.0,
        0 <= j && j < x2.len(),
    ensures
        x2@[j] != 0.0,
{
    proof {
        assert(x2@[j] != 0.0);
    }
}

// </vc-helpers>

// <vc-spec>
fn true_divide(x1: Vec<f64>, x2: Vec<f64>) -> (result: Vec<f64>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2@[i] != 0.0,
    ensures
        result.len() == x1.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implement true_divide using int-index helper */
{
    let n = x1.len();
    let mut result: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
        decreases n - i
    {
        let ji: int = i as int;
        nonzero_index(&x2, ji);
        let v = x1[i] / x2[i];
        result.push(v);
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}