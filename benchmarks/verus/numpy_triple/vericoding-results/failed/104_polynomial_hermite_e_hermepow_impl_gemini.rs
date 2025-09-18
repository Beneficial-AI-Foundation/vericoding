// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added decreases clauses to all loops */
fn polymul(a: &Vec<f64>, b: &Vec<f64>) -> (result: Vec<f64>)
    requires
        a.len() > 0,
        b.len() > 0,
    ensures
        result.len() == a.len() + b.len() - 1,
{
    let n = a.len();
    let m = b.len();
    let result_len = n + m - 1;
    
    let mut res = Vec::new();
    let mut i: usize = 0;
    while i < result_len
        invariant
            i <= result_len,
            res.len() == i,
            forall|j: int| 0 <= j < i ==> res[j] == 0.0
        decreases result_len - i
    {
        res.push(0.0);
        i = i + 1;
    }

    let mut i_a: usize = 0;
    while i_a < n
        invariant
            i_a <= n,
            res.len() == result_len
        decreases n - i_a
    {
        let mut i_b: usize = 0;
        while i_b < m
            invariant
                i_a < n,
                i_b <= m,
                res.len() == result_len
            decreases m - i_b
        {
            let k = i_a + i_b;
            let prev = res[k];
            res.set(k, prev + a[i_a] * b[i_b]);
            i_b = i_b + 1;
        }
        i_a = i_a + 1;
    }
    res
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
    /* code modified by LLM (iteration 2): added decreases clause to the loop */
    if pow == 0 {
        let mut r = Vec::new();
        r.push(1.0);
        return r;
    }

    let mut result = c.clone();
    let mut i: usize = 1;
    while i < pow
        invariant
            1 <= i <= pow,
            result.len() == 1 + (c.len() - 1) * i
        decreases pow - i
    {
        result = polymul(&result, &c);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}