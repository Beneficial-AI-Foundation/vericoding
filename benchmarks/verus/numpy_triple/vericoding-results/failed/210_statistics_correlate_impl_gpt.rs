// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplify proof obligations and avoid casting lengths to int inside proof; provide recursive computation aligned with correlation_sum */
fn correlate_one_from(a: &Vec<i32>, v: &Vec<i32>, k: usize, off: usize) -> (res: i32)
    requires
        off <= v.len(),
        k + v.len() <= a.len(),
    ensures
        res == correlation_sum(a@, v@.skip(off as int), k as int + off as int),
    decreases v.len() - off
{
    if off == v.len() {
        0
    } else {
        assert(off < v.len());
        assert(k + off < a.len());
        let term = a[k + off] * v[off];
        let rest = correlate_one_from(a, v, k, off + 1);
        proof {
            // Align exec and spec indexing for the first term
            assert(a[k + off] == a@[(k as int + off as int)]);
            assert(v[off] == v@[(off as int)]);
            assert(v@.skip(off as int)[0] == v@[(off as int)]);
        }
        term + rest
    }
}

/* helper modified by LLM (iteration 5): thin wrapper starting at offset 0 */
fn correlate_one(a: &Vec<i32>, v: &Vec<i32>, k: usize) -> (res: i32)
    requires
        v.len() > 0,
        k + v.len() <= a.len(),
    ensures
        res == correlation_sum(a@, v@, k as int),
{
    let r = correlate_one_from(a, v, k, 0);
    proof { assert(v@.skip(0) == v@); }
    r
}
// </vc-helpers>

// <vc-spec>
spec fn correlation_sum(a: Seq<i32>, v: Seq<i32>, k: int) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        a[k] * v[0] + correlation_sum(a, v.skip(1), k + 1)
    }
}

fn correlate(a: Vec<i32>, v: Vec<i32>) -> (result: Vec<i32>)
    requires 
        v.len() > 0,
        v.len() <= a.len(),
    ensures
        result.len() == a.len() + 1 - v.len(),
        forall|k: int| 0 <= k < result.len() ==> 
            result[k] == correlation_sum(a@, v@, k),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute correlation for each shift using helper; maintain simple loop invariants */
    let n = a.len();
    let m = v.len();
    let out_len: usize = n + 1 - m;

    let mut result: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < out_len
        invariant
            v.len() > 0,
            v.len() <= a.len(),
            n == a.len(),
            m == v.len(),
            out_len == n + 1 - m,
            k <= out_len,
            k + v.len() <= a.len(),
            result.len() == k,
            forall|i: int| 0 <= i < k as int ==> result[i] == correlation_sum(a@, v@, i),
        decreases out_len - k
    {
        let val = correlate_one(&a, &v, k);
        result.push(val);
        k = k + 1;
    }
    result
}
// </vc-code>


}
fn main() {}