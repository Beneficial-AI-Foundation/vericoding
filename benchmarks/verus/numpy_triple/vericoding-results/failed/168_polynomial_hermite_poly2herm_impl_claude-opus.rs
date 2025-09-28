// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

/* helper modified by LLM (iteration 5): Use f64 loop variable to avoid i32 to f64 cast */
fn hermite_coeff(n: i32, k: i32) -> (result: f64)
    decreases n, k when n >= 0 && k >= 0
{
    if n < 0 || k < 0 {
        0.0
    } else if k > n {
        0.0
    } else if n == 0 {
        if k == 0 { 1.0 } else { 0.0 }
    } else if k == 0 {
        let sign = if n % 2 == 0 { 1.0 } else { -1.0 };
        let mut fact: f64 = 1.0;
        let mut i: f64 = 1.0;
        let n_f64 = n as f64;
        while i <= n_f64
            invariant
                1.0 <= i,
                i <= n_f64 + 1.0
        {
            fact = fact * i;
            i = i + 1.0;
        }
        sign * fact / (2.0_f64.powf(n_f64))
    } else {
        hermite_coeff(n - 1, k - 1) - 
        (2.0 * (n - 1) as f64) * hermite_coeff(n - 2, k - 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn poly2herm(pol: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == pol.len(),

        (forall|i: int| 0 <= i < pol@.len() ==> pol@[i] == 0.0) ==> 
            (forall|i: int| 0 <= i < result@.len() ==> result@[i] == 0.0),

        pol.len() > 0 ==> 
            (forall|i: int| 1 <= i < pol@.len() ==> pol@[i] == 0.0) ==>
                result@[0] == pol@[0],

        (pol.len() == 4 && pol@[0] == 0.0 && pol@[1] == 1.0 && 
         pol@[2] == 2.0 && pol@[3] == 3.0) ==>
            (result@[0] == 1.0 && result@[1] == 2.75 && 
             result@[2] == 0.5 && result@[3] == 0.375)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes needed in code section */
    let mut result = Vec::new();
    let n = pol.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n
    {
        let mut sum = 0.0;
        let mut k: usize = 0;
        while k <= i
            invariant
                k <= i + 1
        {
            sum = sum + pol[k] * hermite_coeff(i as i32, k as i32);
            k = k + 1;
        }
        result.push(sum);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}