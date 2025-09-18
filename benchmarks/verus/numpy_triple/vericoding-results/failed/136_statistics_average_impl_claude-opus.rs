// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn average(a: Vec<f32>, weights: Option<Vec<f32>>) -> (result: f32)
    requires 
        a.len() > 0,
        match weights {
            Some(w) => w.len() == a.len(),
            None => true,
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use f32_add, f32_mul, f32_div for float operations */
    let mut sum: f32 = 0.0;
    let mut weight_sum: f32 = 0.0;
    
    match weights {
        Some(w) => {
            let mut i: usize = 0;
            while i < a.len()
                invariant
                    i <= a.len(),
                    a.len() == w.len(),
                decreases a.len() - i
            {
                let ai = a[i];
                let wi = w[i];
                sum = f32_add(sum, f32_mul(ai, wi));
                weight_sum = f32_add(weight_sum, wi);
                i = i + 1;
            }
            if weight_sum == 0.0 {
                0.0
            } else {
                f32_div(sum, weight_sum)
            }
        },
        None => {
            let mut i: usize = 0;
            let mut count: f32 = 0.0;
            while i < a.len()
                invariant
                    i <= a.len(),
                decreases a.len() - i
            {
                let ai = a[i];
                sum = f32_add(sum, ai);
                count = f32_add(count, 1.0);
                i = i + 1;
            }
            f32_div(sum, count)
        }
    }
}
// </vc-code>

}
fn main() {}