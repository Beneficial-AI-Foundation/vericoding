// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed assert statements by adding 'as int' casts to both sides of comparisons for type compatibility in ghost assertions. */
fn poly_mul(a: Vec<f64>, b: Vec::<f64>) -> (result: Vec<f64>)
    requires
        a.len() > 0,
        b.len() > 0,
        forall |i: int| 0 <= i < a.len() ==> a[i].is_finite(),
        forall |i: int| 0 <= i < b.len() ==> b[i].is_finite(),
    ensures
        result.len() == a.len() + b.len() - 1,
        forall |i: int| 0 <= i < result.len() ==> result[i].is_finite(),
{
    let n = a.len() + b.len() - 1;
    let mut result = Vec::<f64>::with_capacity(n as usize);
    for i in 0..n {
        let mut sum = 0.0;
        for j in 0..a.len() {
            if i >= j && i - j < b.len() {
                proof {
                    assert(j as int < a.len() as int);
                    assert((i as int - j as int >= 0) && (i - j) as int < b.len() as int);
                }
                sum += a[j] * b[i - j];
            }
        }
        result.push(sum);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn chebpow(c: Vec<f64>, pow: u8, maxpower: u8) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
        pow <= maxpower,
    ensures
        /* Special case: pow = 0 returns [1.0] */
        (pow as nat == 0) ==> (result.len() == 1 && result[0] == 1.0),
        /* Special case: pow = 1 returns input unchanged */
        (pow as nat == 1) ==> (result.len() == c.len() && 
            forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),
        /* Result length is correct */
        result.len() == (if pow as nat == 0 { 1 } else { 1 + (c.len() - 1) * pow as nat }),
        /* For pow > 1: first coefficient exists when appropriate */
        (pow as nat > 1 && c.len() >= 1) ==> (result.len() > 0),
        /* Non-triviality for pow >= 2 with sufficient input length */
        (pow as nat >= 2 && c.len() >= 2 && result.len() > 2) ==> 
            (result[0] != 0.0 || result[1] != 0.0 || result[2] != 0.0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes required, keeping the recursive multiplication implementation using poly_mul helper. */
{
 if pow == 0 {
     let mut result = Vec::new();
     result.push(1.0);
     result
 } else if pow == 1 {
     c
 } else {
     let mut result = c.clone();
     for _ in 1..pow {
         proof {
             assert(result.len() > 0);
             assert(c.len() > 0);
         }
         result = poly_mul(result, c.clone());
     }
     result
 }
}
// </vc-code>


}
fn main() {}