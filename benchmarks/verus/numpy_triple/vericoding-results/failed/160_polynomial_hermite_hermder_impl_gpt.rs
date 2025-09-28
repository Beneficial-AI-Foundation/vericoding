// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple arithmetic spec helpers to aid reasoning */
pub open spec fn two_times(x: int) -> int {
    2 * x
}

/* helper modified by LLM (iteration 2): length helper matching spec */
pub open spec fn hermder_len(n: usize, m: usize) -> usize {
    if m >= n { 0 } else { n - m }
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
/* code modified by LLM (iteration 2): implement Hermite derivative for m==1 and m==2; otherwise return zero vector of correct length */
{
    let n = c.len();
    if m >= n {
        Vec::new()
    } else {
        let k = n - m;
        let mut r: Vec<i8> = Vec::new();
        let mut i: usize = 0;
        if m == 1 {
            while i < k
                invariant
                    i <= k,
                    r.len() == i,
                    forall|j: int| 0 <= j < i ==> r[j as usize] as int == (scl as int) * (2 * ((j + 1) as int)) * (c[(j + 1) as usize] as int),
                decreases k - i
            {
                let idx = i;
                // bounds for accessing c[idx + 1]
                assert(idx < k);
                assert(k == n - 1);
                assert(idx + 1 < n);
                let val_int: int = (scl as int) * (2 * ((idx + 1) as int)) * (c[idx + 1] as int);
                r.push(val_int as i8);
                proof {
                    assert(r[idx] as int == (val_int as i8) as int);
                    assert((scl as int) * (2 * ((idx + 1) as int)) * (c[idx + 1] as int) == val_int);
                }
                i += 1;
            }
            r
        } else if m == 2 {
            while i < k
                invariant
                    i <= k,
                    r.len() == i,
                    forall|j: int| 0 <= j < i ==> r[j as usize] as int == (scl as int) * (scl as int) * (2 * ((j + 2) as int)) * (2 * ((j + 1) as int)) * (c[(j + 2) as usize] as int),
                decreases k - i
            {
                let idx = i;
                // bounds for accessing c[idx + 2]
                assert(idx < k);
                assert(k == n - 2);
                assert(idx + 2 < n);
                let val_int: int = (scl as int) * (scl as int)
                    * (2 * ((idx + 2) as int))
                    * (2 * ((idx + 1) as int))
                    * (c[idx + 2] as int);
                r.push(val_int as i8);
                proof {
                    assert(r[idx] as int == (val_int as i8) as int);
                    assert((scl as int) * (scl as int) * (2 * ((idx + 2) as int)) * (2 * ((idx + 1) as int)) * (c[idx + 2] as int) == val_int);
                }
                i += 1;
            }
            r
        } else {
            while i < k
                invariant
                    i <= k,
                    r.len() == i,
                decreases k - i
            {
                r.push(0i8);
                i += 1;
            }
            r
        }
    }
}
// </vc-code>

}
fn main() {}