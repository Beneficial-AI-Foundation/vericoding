// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed index assignment for f64 */
fn hermepow_recursive(c: Vec<f64>, curr_pow: u8, target_pow: u8, maxpower: u8) -> (result: Vec<f64>)
    requires 
        curr_pow <= target_pow,
        target_pow <= maxpower,
        maxpower <= 16,
        c.len() > 0,
    ensures
        curr_pow == 0 ==> result.len() == 1 && result[0] == 1.0 && 
            (forall|i: int| 1 <= i < result.len() ==> result[i] == 0.0),
        curr_pow == 1 ==> result.len() == c.len() &&
            (forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),
        curr_pow as int >= 1 ==> result.len() == 1 + (c.len() - 1) * curr_pow as int,
        curr_pow as int >= 1 && c.len() > 0 ==> result.len() > 0,
{
    if curr_pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        result
    } else if curr_pow == 1 {
        c
    } else {
        let prev = hermepow_recursive(c, curr_pow - 1, target_pow, maxpower);
        let mut result = Vec::new();
        let n = c.len();
        let prev_len = prev.len();
        
        for i in 0..prev_len {
            result.push(0.0);
        }
        
        for i in 0..prev_len {
            for j in 0..n {
                let idx = i + j;
                if idx < result.len() {
                    result[idx] = result[idx] + prev[i] * c[j];
                }
            }
        }
        
        result
    }
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
{
    /* code modified by LLM (iteration 2): implemented hermepow using recursive helper */
    hermepow_recursive(c, pow, pow, maxpower)
}
// </vc-code>

}
fn main() {}