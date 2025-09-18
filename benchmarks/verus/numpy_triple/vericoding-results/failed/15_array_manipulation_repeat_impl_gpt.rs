// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove i / m < n from 0 <= i < n*m and m > 0 using division algorithm facts */
proof fn div_bound_implies_lt(i: int, m: int, n: int)
    requires 0 <= i, 0 < m, i < n * m
    ensures i / m < n
{
    let q = i / m;
    let r = i % m;
    assert(q * m + r == i);
    assert(0 <= r);
    assert(r < m);
    assert(q * m <= i);
    assert(q * m < n * m);
    assert(q < n);
}
// </vc-helpers>

// <vc-spec>
fn repeat<T: Copy>(a: Vec<T>, repeats: usize) -> (result: Vec<T>)
    requires repeats > 0,
    ensures
        result.len() == a.len() * repeats,
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
            let k = i / (repeats as int);
            0 <= k < a.len() && result[i] == a[k]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented nested loops to build repeated array; use ghost int for repeats to avoid exec-int usage */
    let n = a.len();
    let ghost r_int: int = repeats as int;
    let ghost a_seq = a@;

    let mut out: Vec<T> = Vec::new();

    let mut k: usize = 0;
    while k < n
        invariant
            a@ == a_seq,
            n == a.len(),
            r_int == repeats as int,
            k <= n,
            out.len() == k * repeats,
            forall|i: int| #![trigger out@[i]] 0 <= i < out.len() ==> {
                let kk = i / r_int;
                0 <= kk <= k as int && out@[i] == a_seq[kk]
            }
        decreases n - k
    {
        let elem = a[k];
        let mut r: usize = 0;
        while r < repeats
            invariant
                a@ == a_seq,
                n == a.len(),
                r_int == repeats as int,
                k < n,
                r <= repeats,
                out.len() == k * repeats + r,
                forall|i: int| #![trigger out@[i]] 0 <= i < out.len() ==> {
                    let kk = i / r_int;
                    0 <= kk <= k as int && out@[i] == a_seq[kk]
                }
            decreases repeats - r
        {
            out.push(elem);
            r += 1;
        }
        k += 1;
    }

    out
}
// </vc-code>

}
fn main() {}