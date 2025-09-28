// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute first-derivative element */
fn compute_m1_elem(scl: i8, i: usize, c: &Vec<i8>) -> (result: i8)
    requires
        i + 1 < c.len(),
    ensures
        result as int == (scl as int) * (2 * ((i + 1) as int)) * (c[i + 1] as int),
{
    let tmp: i32 = (scl as i32) * (2 * ((i + 1) as i32)) * (c[i + 1] as i32);
    let r: i8 = #[verifier::truncate] tmp as i8;
    proof {
        let v_int: int = (scl as int) * (2 * ((i + 1) as int)) * (c[i + 1] as int);
        assert(tmp as int == v_int);
        assert(r as int == v_int);
    }
    r
}

/* helper modified by LLM (iteration 5): compute second-derivative element */
fn compute_m2_elem(scl: i8, i: usize, c: &Vec<i8>) -> (result: i8)
    requires
        i + 2 < c.len(),
    ensures
        result as int == (scl as int) * (scl as int) * (2 * ((i + 2) as int)) * (2 * ((i + 1) as int)) * (c[i + 2] as int),
{
    let tmp: i32 = (scl as i32) * (scl as i32) * (2 * ((i + 2) as i32)) * (2 * ((i + 1) as i32)) * (c[i + 2] as i32);
    let r: i8 = #[verifier::truncate] tmp as i8;
    proof {
        let v_int: int = (scl as int) * (scl as int) * (2 * ((i + 2) as int)) * (2 * ((i + 1) as int)) * (c[i + 2] as int);
        assert(tmp as int == v_int);
        assert(r as int == v_int);
    }
    r
}
// </vc-helpers>

// <vc-spec>
fn hermder(c: Vec<i8>, m: usize, scl: i8) -> (result: Vec<i8>)
    ensures
        result.len() == if m >= c.len() { 0 } else { c.len() - m },
        m >= c.len() ==> result.len() == 0,
        m < c.len() ==> result.len() == c.len() - m,
        (m == 1 && c.len() > 0) ==> (
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] as int == (scl as int) * (2 * ((i + 1) as int)) * (c[i + 1] as int)
        ),
        (m == 2 && c.len() > 1) ==> (
            forall|i: int| 0 <= i < result.len() ==>
                result[i] as int == (scl as int) * (scl as int) * (2 * ((i + 2) as int)) * (2 * ((i + 1) as int)) * (c[i + 2] as int)
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement hermder using helpers and handle lengths with proofs */
    let n = c.len();
    if m >= n {
        return Vec::new();
    }
    let res_len = n - m;
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < res_len
        invariant
            i <= res_len,
            result.len() == i,
        decreases res_len - i
    {
        if m == 1 {
            proof {
                assert(i < res_len);
                assert(res_len + m == n);
                assert(m == 1);
                assert(i + 1 < n);
            }
            let v = compute_m1_elem(scl, i, &c);
            result.push(v);
        } else if m == 2 {
            proof {
                assert(i < res_len);
                assert(res_len + m == n);
                assert(m == 2);
                assert(i + 2 < n);
            }
            let v = compute_m2_elem(scl, i, &c);
            result.push(v);
        } else {
            result.push(0i8);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}