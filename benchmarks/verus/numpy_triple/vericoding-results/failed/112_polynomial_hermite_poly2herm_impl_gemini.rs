// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn poly2herm(pol: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == pol.len(),

        (forall|i: int| 0 <= i < pol.len() ==> pol[i] == 0.0) ==> 
            (forall|i: int| 0 <= i < result.len() ==> result[i] == 0.0),

        pol.len() > 0 ==> 
            (forall|i: int| 1 <= i < pol.len() ==> pol[i] == 0.0) ==>
                result[0] == pol[0],

        (pol.len() == 4 && pol[0] == 0.0 && pol[1] == 1.0 && 
         pol[2] == 2.0 && pol[3] == 3.0) ==>
            (result[0] == 1.0 && result[1] == 2.75 && 
             result[2] == 0.5 && result[3] == 0.375)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed unsupported f64 comparison from invariant to fix compilation error. */
    let n = pol.len();
    if n == 0 {
        let result: Vec<f64> = Vec::new();
        return result;
    }

    let mut result: Vec<f64> = Vec::new();
    result.resize(n, 0.0);

    let mut i = n;
    while i > 0
        invariant
            pol.len() == n,
            result.len() == n,
        decreases i
    {
        i = i - 1;
        let c = pol[i];
        let h_old = result.clone();

        let h1 = if n > 1 { h_old[1] } else { 0.0 };
        result.set(0, c + h1);

        let mut j: usize = 1;
        let mut j_f64: f64 = 1.0;
        while j < n
            invariant
                pol.len() == n,
                result.len() == n,
                h_old.len() == n,
                1 <= j,
                j <= n,
            decreases n - j
        {
            let term1 = h_old[j - 1] / 2.0;
            let term2 = if j + 1 < n {
                h_old[j + 1] * (j_f64 + 1.0)
            } else {
                0.0
            };
            result.set(j, term1 + term2);
            j = j + 1;
            j_f64 = j_f64 + 1.0;
        }
    }
    result
}
// </vc-code>

}
fn main() {}