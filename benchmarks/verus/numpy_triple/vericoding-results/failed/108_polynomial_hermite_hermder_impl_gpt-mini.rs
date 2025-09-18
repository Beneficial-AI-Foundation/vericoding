// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): integer power function */
fn pow_i32(s: i32, e: usize) -> i32 {
    let mut res64: i64 = 1;
    let mut i: usize = 0;
    while i < e
        invariant i <= e,
        decreases e - i
    {
        res64 = res64 * (s as i64);
        i += 1;
    }
    #[verifier::truncate]
    res64 as i32
}

/* helper modified by LLM (iteration 5): product of 2*(i0+1)..2*(i0+m) */
fn two_mult(i0: usize, m: usize) -> i32 {
    let mut prod64: i64 = 1;
    let mut t: usize = 0;
    while t < m
        invariant t <= m,
        decreases m - t
    {
        prod64 = prod64 * (2 * ((i0 + t + 1) as i64));
        t += 1;
    }
    #[verifier::truncate]
    prod64 as i32
}
// </vc-helpers>

// <vc-spec>
fn hermder(c: Vec<i32>, m: usize, scl: i32) -> (result: Vec<i32>)
    ensures
        result.len() == if m >= c.len() { 0 } else { c.len() - m },
        m >= c.len() ==> result.len() == 0,
        m < c.len() ==> result.len() == c.len() - m,
        (m == 1 && c.len() > 0) ==> (
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] == scl * (2 * ((i + 1) as i32)) * c[i + 1]
        ),
        (m == 2 && c.len() > 1) ==> (
            forall|i: int| 0 <= i < result.len() ==>
                result[i] == scl * scl * (2 * ((i + 2) as i32)) * (2 * ((i + 1) as i32)) * c[i + 2]
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute m-th Hermite derivative coefficients with invariants and proofs */
    let n = c.len();
    if m >= n {
        return Vec::<i32>::new();
    }
    let out_len = n - m;
    let mut res: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < out_len
        invariant idx <= out_len,
        invariant res.len() == idx,
        invariant forall|j: int| 0 <= j && j < idx as int ==>
            res[j as usize] == pow_i32(scl, m) * two_mult(j as usize, m) * c[(j as usize) + m],
        decreases out_len - idx
    {
        proof {
            assert(idx < out_len);
            assert(idx + m < n);
        }
        let coeff = c[idx + m];
        let prod = two_mult(idx, m);
        let sp = pow_i32(scl, m);
        let val = sp * prod * coeff;
        res.push(val);
        idx += 1;
    }
    res
}
// </vc-code>

}
fn main() {}