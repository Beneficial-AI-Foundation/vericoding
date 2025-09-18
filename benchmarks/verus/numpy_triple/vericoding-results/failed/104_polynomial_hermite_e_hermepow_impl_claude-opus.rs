// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clause to hermite_multiply helper function */
fn hermite_multiply(a: Vec<f64>, b: Vec<f64>) -> (result: Vec<f64>)
    requires
        a.len() > 0,
        b.len() > 0,
    ensures
        result.len() == a.len() + b.len() - 1,
{
    let mut result = Vec::new();
    let n = a.len() + b.len() - 1;
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            n == a.len() + b.len() - 1,
        decreases n - i,
    {
        let mut sum = 0.0;
        let mut j = 0;
        while j <= i
            invariant
                0 <= j <= i + 1,
            decreases i - j + 1,
        {
            if j < a.len() && i - j < b.len() {
                sum = sum + a[j] * b[i - j];
            }
            j = j + 1;
        }
        result.push(sum);
        i = i + 1;
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
/* code modified by LLM (iteration 5): Fixed syntax by removing incorrect decreases clause placement */
{
    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        result
    } else if pow == 1 {
        let mut result = Vec::new();
        let mut i = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result[j] == c[j],
            decreases c.len() - i,
        {
            result.push(c[i]);
            i = i + 1;
        }
        result
    } else {
        let mut result = hermepow(c.clone(), pow / 2, maxpower);
        result = hermite_multiply(result.clone(), result);
        if pow % 2 == 1 {
            result = hermite_multiply(result, c.clone());
        }
        result
    }
}
// </vc-code>

}
fn main() {}