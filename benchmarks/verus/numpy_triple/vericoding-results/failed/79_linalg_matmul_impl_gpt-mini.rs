// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): construct a row of length n filled with v */
fn make_row(n: usize, v: i8) -> (result: Vec<i8>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < (n as int) ==> #[trigger] result@[i] == v,
{
    let mut row: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            row.len() == i,
        decreases n - i
    {
        row.push(v);
        i = i + 1;
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn matmul(A: Vec<Vec<i8>>, B: Vec<Vec<i8>>) -> (result: Vec<Vec<i8>>)
    requires
        A.len() > 0,
        B.len() > 0,
        A@[0].len() == B.len(),
        forall|i: int| 0 <= i < A.len() ==> #[trigger] A@[i].len() == A@[0].len(),
        forall|i: int| 0 <= i < B.len() ==> #[trigger] B@[i].len() == B@[0].len(),
    ensures
        result.len() == A.len(),
        result.len() > 0 ==> result@[0].len() == B@[0].len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result@[i].len() == B@[0].len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement matmul and fix verifier truncate casts */
    let m: usize = A.len();
    let n: usize = B[0].len();
    let k: usize = A[0].len();

    let mut result: Vec<Vec<i8>> = Vec::new();

    let mut i: usize = 0;
    while i < m
        invariant
            i <= m,
            result.len() == i,
            forall|t: int| 0 <= t < (i as int) ==> #[trigger] result@[t].len() == n,
        decreases m - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                row.len() == j,
            decreases n - j
        {
            let mut sum: i32 = 0;
            let mut kk: usize = 0;
            while kk < k
                invariant
                    kk <= k,
                decreases k - kk
            {
                proof {
                    assert(i < A.len());
                    assert(#[verifier::truncate] i as int >= 0);
                    assert(#[verifier::truncate] i as int < (A.len() as int));
                    assert(A@[(#[verifier::truncate] i as int)].len() == k);

                    assert(kk < k);
                    assert(#[verifier::truncate] kk as int >= 0);
                    assert(#[verifier::truncate] kk as int < (k as int));
                    assert(k == A[0].len());
                    assert(A@[0].len() == B.len());
                    assert(B.len() == k);
                    assert(B@[(#[verifier::truncate] kk as int)].len() == B@[(0 as int)].len());
                    assert(B@[(0 as int)].len() == n);
                }
                sum = sum + (A[i][kk] as i32) * (B[kk][j] as i32);
                kk = kk + 1;
            }
            row.push(#[verifier::truncate] sum as i8);
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}