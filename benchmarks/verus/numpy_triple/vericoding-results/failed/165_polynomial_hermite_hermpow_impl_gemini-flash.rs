// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unused helper for polynomial multiplication. */
// </vc-helpers>

// <vc-spec>
fn hermpow(c: Vec<f64>, pow: usize, maxpower: usize) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
    ensures

        result.len() <= maxpower + 1,
        result.len() == if c.len() + (c.len() - 1) * pow <= maxpower + 1 {
            c.len() + (c.len() - 1) * pow
        } else {
            maxpower + 1
        },

        pow == 0 ==> result.len() == 1 && result[0] == 1.0,

        (pow == 1 && c.len() <= maxpower + 1) ==> (
            result.len() == c.len() &&
            forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]
        ),

        ((exists|i: int| 0 <= i < c.len() && c[i] != 0.0) && pow > 0) ==> 
            exists|j: int| 0 <= j < result.len() && result[j] != 0.0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected `term_sum` invariant to use a comma-separated list of function calls instead of `map().fold()`. */
    let c_len = c.len();

    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        return result;
    }

    if pow == 1 {
        let mut result = Vec::new();
        let mut i = 0;
        while i < c_len 
            invariant
                0 <= i <= c_len,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result.contains_exact_element(c[j] as f64),
        {
            result.push(c[i]);
            i = i + 1;
        }
        if result.len() > maxpower + 1 {
            result.truncate(maxpower + 1);
        }
        return result;
    }

    let mut current_product = Vec::new();
    let mut i = 0;
    while i < c_len
        invariant
            0 <= i <= c_len,
            current_product.len() == i,
            forall|j: int| 0 <= j < i ==> current_product.contains_exact_element(c[j] as f64),
    {
        current_product.push(c[i]);
        i = i + 1;
    }

    let mut p = 1;

    while p < pow
        invariant
            1 <= p <= pow,
            current_product.len() <= maxpower + 1 + (pow - p) * c_len,
            (p == 1 && c.len() <= maxpower + 1) ==> (current_product.len() == c.len()),

            forall|k: int| 0 <= k < current_product.len() ==> 
                (exists|i: int| k == i * p && 0 <= i < c_len ),

            ((exists|idx: int| 0 <= idx < c.len() && c[idx] != 0.0) && p > 0) ==> 
                exists|j: int| 0 <= j < current_product.len() && current_product[j] != 0.0,
    {
        let mut next_product = Vec::new();
        let max_next_len = current_product.len() + c_len - 1;
        let output_len = if max_next_len <= maxpower + 1 { max_next_len } else { maxpower + 1 }; 

        let mut k = 0;
        while k < output_len
            invariant
                0 <= k <= output_len,
                next_product.len() == k,
                next_product.len() <= maxpower + 1,
                
                ((exists|idx: int| 0 <= idx < c.len() && c[idx] != 0.0)
                 && (exists|jdx: int| 0 <= jdx < current_product.len() && current_product[jdx] != 0.0)) ==> 
                    exists|x: int| 0 <= x < k && next_product[x] != 0.0,
        {
            let mut term_sum = 0.0;
            let mut i = 0;

            while i < c_len
                invariant
                    0 <= i <= c_len,
                    term_sum == (0..i)
                        .filter(|inner_idx: int|
                            0 <= k - inner_idx && (k - inner_idx) < current_product.len()
                        )
                        .map_values(|inner_idx: int| c[inner_idx] * current_product[k - inner_idx])
                        .fold(0.0, |acc: f64, v: f64| acc + v),
            {
                if (k as int) - (i as int) >= 0 && (k as int) - (i as int) < current_product.len() as int {
                    term_sum += c[i] * current_product[k - i];
                }
                i = i + 1;
            }
            next_product.push(term_sum);
            k = k + 1;
        }
        current_product = next_product;
        p = p + 1;
    }
    
    let mut final_result = Vec::new();
    let mut i = 0;
    let limit = if current_product.len() <= maxpower + 1 { current_product.len() } else { maxpower + 1 };
    while i < limit
        invariant
         0 <= i <= limit,
         final_result.len() == i,
         forall |j: int| 0 <= j < i ==> final_result.contains_exact_element(current_product[j]),
    {
        final_result.push(current_product[i]);
        i = i + 1;
    }

    final_result
}
// </vc-code>

}
fn main() {}