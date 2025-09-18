// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn poly_mul(a: Vec<f64>, b: Vec<f64>) -> Vec<f64> {
    let mut result = vec![];
    for _ in 0..(a.len() + b.len() - 1) {
        result.push(0.0);
    }
    for i in 0..a.len() {
        for j in 0..b.len() {
            result[i + j] = result[i + j] + a[i] * b[j];
        }
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn hermepow(c: Vec<f64>, pow: usize, maxpower: usize) -> (result: Vec<f64>)
    requires 
        pow <= maxpower,
        maxpower <= 16,
        c.len() > 0,
    ensures

        pow == 0 ==> result.len() == 1 && result[0] == 1.0 && 
            (forall|i: int| #![trigger result[i]] 1 <= i < result.len() ==> result[i] == 0.0),
        pow == 1 ==> result.len() == c.len() &&
            (forall|i: int| #![trigger result[i]] 0 <= i < c.len() ==> result[i] == c[i]),

        pow >= 1 ==> result.len() == 1 + (c.len() - 1) * pow,

        true, // Highest coefficient exists (simplified)
// </vc-spec>
// <vc-code>
{
    if pow == 0 {
        vec![1.0]
    } else {
        let mut result = vec![1.0];
        for _ in 0..pow {
            result = poly_mul(result, c.clone());
        }
        result
    }
}
// </vc-code>

}
fn main() {}