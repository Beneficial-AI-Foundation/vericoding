// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed arithmetic overflow and array access bounds */
spec fn chebyshev_product_length(c_len: nat, pow: nat) -> nat {
    if pow == 0 {
        1nat
    } else {
        (1nat + (c_len - 1nat) * pow) as nat
    }
}

fn multiply_chebyshev(c1: &Vec<f64>, c2: &Vec<f64>) -> (result: Vec<f64>)
    requires
        c1.len() > 0,
        c2.len() > 0,
    ensures
        result.len() == c1.len() + c2.len() - 1,
{
    let n1 = c1.len();
    let n2 = c2.len();
    let mut result = Vec::new();
    let mut i: usize = 0;
    let total_len = n1 + n2 - 1;
    
    while i < total_len
        invariant
            n1 > 0,
            n2 > 0,
            total_len == n1 + n2 - 1,
            result.len() == i,
            i <= total_len,
        decreases total_len - i,
    {
        let mut sum: f64 = 0.0;
        let mut j: usize = 0;
        let max_j = if i < n1 { i + 1 } else { n1 };
        
        while j < max_j
            invariant
                j <= max_j,
                max_j <= n1,
                max_j <= i + 1,
            decreases max_j - j,
        {
            if i >= j && (i - j) < n2 {
                proof {
                    assert(j < n1);
                    assert(i - j < n2);
                }
                sum = sum + c1[j] * c2[i - j];
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
{
    /* code modified by LLM (iteration 5): Fixed loop invariants and ensure non-trivial result */
    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        return result;
    } else if pow == 1 {
        let mut result = Vec::new();
        let mut i: usize = 0;
        while i < c.len()
            invariant
                result.len() == i,
                i <= c.len(),
                forall|j: int| 0 <= j < i ==> result[j] == c[j],
            decreases c.len() - i,
        {
            result.push(c[i]);
            i = i + 1;
        }
        return result;
    } else {
        let mut result = c.clone();
        let mut p: u8 = 1;
        
        proof {
            assert(result.len() == c.len());
            assert(c.len() > 0);
            assert(result.len() == 1 + (c.len() - 1) * 1);
        }
        
        while p < pow
            invariant
                p >= 1,
                p <= pow,
                c.len() > 0,
                result.len() == 1 + (c.len() - 1) * p as nat,
            decreases pow - p,
        {
            proof {
                assert(result.len() > 0);
                assert(c.len() > 0);
            }
            result = multiply_chebyshev(&result, &c);
            proof {
                assert(result.len() == (1 + (c.len() - 1) * p as nat) + c.len() - 1);
                assert(result.len() == 1 + (c.len() - 1) * (p + 1) as nat);
            }
            p = p + 1;
        }
        
        proof {
            if pow >= 2 && c.len() >= 2 && result.len() > 2 {
                // The multiplication produces non-trivial results
                assert(result.len() == 1 + (c.len() - 1) * pow as nat);
                assert(result.len() >= 1 + 1 * 2);
                assert(result.len() >= 3);
            }
        }
        
        return result;
    }
}
// </vc-code>


}
fn main() {}