// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed loop range to use exclusive range instead of inclusive. */
fn multiply(a: &Vec<f64>, b: &Vec<f64>) -> (result: Vec<f64>)
    requires
        a.len() > 0,
        b.len() > 0,
    ensures
        result.len() == a.len() + b.len() - 1,
{
    let rlen = a.len() + b.len() - 1;
    let mut result = Vec::with_capacity(rlen);
    for i in 0..rlen {
        let mut sum = 0.0;
        for j in 0..(i+1) {
            let idx1 = j;
            let idx2 = i - j;
            if idx1 < a.len() && idx2 < b.len() {
                sum += a[idx1] * b[idx2];
            }
        }
        result.push(sum);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn hermepow(c: Vec<f64>, pow: u8, maxpower: u8) -> (result: Vec<f64>)
    requires 
        pow <= maxpower,
        maxpower <= 16,
        c.len() > 0,
    ensures

        pow == 0 ==> result.len() == 1 && result[0] == 1.0 && 
            (forall|i: int| 1 <= i < result.len() ==> result[i] == 0.0),
        pow == 1 ==> result.len() == c.len() &&
            (forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),

        pow as int >= 1 ==> result.len() == 1 + (c.len() - 1) * pow as int,

        pow as int >= 1 && c.len() > 0 ==> result.len() > 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Implemented polynomial power computation using iterative multiplication. */
{
    if pow == 0 {
        vec![1.0]
    } else {
        let mut result = c.clone();
        let mut current_power = 1u8;
        while current_power < pow
            invariant
                current_power >= 1,
                current_power <= pow,
                result.len() == 1 + ((c.len() - 1) as int * (current_power as int)),
            decreases (pow - current_power)
        {
            result = multiply(&result, &c);
            current_power += 1;
        }
        result
    }
}
// </vc-code>

}
fn main() {}