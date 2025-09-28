// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): ensures int bounds from usize bound for quantifier instantiation */
pub proof fn usize_lt_to_int_lt(i: usize, n: usize)
    requires
        i < n,
    ensures
        0 <= i as int,
        (i as int) < n as int,
{
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
{
    /* code modified by LLM (iteration 5): strengthen quantifier instantiation to prove non-zero divisors before division */
    let n = x1.len();
    let mut result: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            x1.len() == n,
            x2.len() == n,
            i <= n,
            result.len() == i,
        decreases n - i
    {
        let a = x1[i];
        let b = x2[i];
        proof {
            // Establish integer bounds for i to instantiate the precondition quantifier
            usize_lt_to_int_lt(i, n);
            let k = i as int;
            assert(0 <= k);
            assert(k < x2.len());
            // From the requires clause: 0 <= k < x2.len() ==> x2@[k] != 0.0
            assert(x2@[k] != 0.0);
            // Link exec indexing with spec view
            assert(b == x2@[k]);
        }
        assert(b != 0.0);
        result.push(a / b);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}