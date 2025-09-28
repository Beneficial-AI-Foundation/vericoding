// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_mod_mul_add(m: int, r: int, j: int)
    requires
        m > 0,
        0 <= j,
    ensures
        (m * r + j) % m == j % m,
{
}

proof fn lemma_mod_small(j: int, m: int)
    requires
        m > 0,
        0 <= j,
        j < m,
    ensures
        j % m == j,
{
}
// </vc-helpers>

// <vc-spec>
fn tile(a: Vec<i32>, reps: usize) -> (result: Vec<i32>)
    requires 
        reps > 0,
        a.len() > 0,
    ensures
        result.len() == a.len() * reps,
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i % (a.len() as int)],
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut result: Vec<i32> = Vec::new();
    let mut r: usize = 0;
    while r < reps
        invariant
            reps > 0,
            n > 0,
            r <= reps,
            result.len() == n * r,
            forall|k: int|
                0 <= k < result.len() ==> result[k] == a[k % (n as int)],
        decreases reps - r
    {
        let mut j: usize = 0;
        while j < n
            invariant
                reps > 0,
                n > 0,
                r <= reps,
                j <= n,
                result.len() == n * r + j,
                forall|k: int|
                    0 <= k < result.len() ==> result[k] == a[k % (n as int)],
            decreases n - j
        {
            let val = a[j];
            result.push(val);
            j = j + 1;
            proof {
                assert(j > 0);
                let m = n as int;
                let rr = r as int;
                let jjm1 = (j as int) - 1;
                assert(0 <= jjm1);
                assert(jjm1 < m) by {
                    assert(j <= n);
                }
                lemma_mod_mul_add(m, rr, jjm1);
                lemma_mod_small(jjm1, m);
                let new_len = result.len() as int;
                assert(new_len > 0);
                assert(result[new_len - 1] == a[jjm1]);
            }
        }
        r = r + 1;
    }
    result
}
// </vc-code>

}
fn main() {}