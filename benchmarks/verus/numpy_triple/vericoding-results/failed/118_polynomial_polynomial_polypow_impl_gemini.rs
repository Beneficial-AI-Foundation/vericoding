// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes */
fn polymul(a: Vec<f32>, b: Vec<f32>) -> (result: Vec<f32>)
{
    let n = a.len();
    let m = b.len();
    if n == 0 || m == 0 {
        return Vec::new();
    }
    let res_len = n + m - 1;
    
    let mut res = Vec::new();
    let mut k: usize = 0;
    while k < res_len
        invariant
            0 <= k <= res_len,
            res.len() == k,
    {
        res.push(0.0f32);
        k = k + 1;
    }

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            res.len() == res_len,
    {
        let mut j: usize = 0;
        while j < m
            invariant
                0 <= j <= m,
                0 <= i < n,
                res.len() == res_len,
        {
            let index = i + j;
            res.set(index, res[index] + a[i] * b[j]);
            j = j + 1;
        }
        i = i + 1;
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn polypow(c: Vec<f32>, pow: nat) -> (result: Vec<f32>)
    ensures
        pow == 0 ==> (result.len() == 1 && result[0] == 1.0f32),
        pow == 1 ==> result.len() == c.len() && (forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type mismatches by casting integer literals to nat */
{
    if pow == 0 as nat {
        let mut v = Vec::new();
        v.push(1.0f32);
        return v;
    }

    if c.len() == 0 {
        return Vec::new();
    }

    let mut result = c.clone();
    let mut i: nat = 1 as nat;
    while i < pow
        invariant
            pow > 0,
            1 <= i && i <= pow,
            c.len() > 0,
            decreases pow - i,
    {
        result = polymul(result, c.clone());
        i = i + (1 as nat);
    }

    result
}
// </vc-code>

}
fn main() {}