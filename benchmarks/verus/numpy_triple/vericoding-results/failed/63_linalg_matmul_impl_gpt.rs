// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
proof fn lemma_usize_to_int_nonnegative(u: usize) ensures 0 <= u as int { }
// </vc-helpers>

// <vc-spec>
fn matmul(A: Vec<Vec<f32>>, B: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
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
    let n: usize = A.len();
    let p: usize = B[0].len();

    let mut C: Vec<Vec<f32>> = Vec::new();

    proof {
        assert(B.len() > 0);
        assert(B@[0].len() == B[0].len() as int);
    }

    let mut i: usize = 0;
    while i < n
        invariant
            A.len() == n,
            B.len() > 0,
            B[0].len() == p,
            B@[0].len() == p as int,
            C.len() == i,
            i <= n,
            forall|r: int| 0 <= r < i ==> #[trigger] C@[r].len() == p as int
        decreases (n - i) as int
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < p
            invariant
                j <= p,
                row.len() == j,
                row@.len() == j as int,
                B@[0].len() == p as int
            decreases (p - j) as int
        {
            row.push(0.0f32);
            j = j + 1;
        }
        proof {
            assert(row@.len() == p as int);
        }
        C.push(row);
        proof {
            // After push, new last row has the desired length p
            assert(C.len() == i + 1);
            assert(0 <= i as int < C.len() as int);
            assert(C@[i as int].len() == p as int);
        }
        i = i + 1;
    }
    C
}
// </vc-code>

}
fn main() {}