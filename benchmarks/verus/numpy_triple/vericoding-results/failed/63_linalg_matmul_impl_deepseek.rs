// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added result variable helper and fixed verification */
spec fn result_spec() -> Vec<Vec<f32>> {
    Vec::new()
}

proof fn matrix_dimensions_consistent<T>(v: Vec<Vec<T>>) 
    requires v.len() > 0 && forall|i: int| 0 <= i < v.len() ==> v@[i].len() == v@[0].len()
    ensures forall|i: int| 0 <= i < v.len() ==> v@[i].len() == v@[0].len()
{
}

spec fn dot_product(a: Seq<f32>, b: Seq<f32>) -> f32 
    requires a.len() == b.len()
    decreases a.len()
{
    if a.len() == 0 {
        0.0
    } else {
        a[0] * b[0] + dot_product(a.subrange(1, a.len() as int), b.subrange(1, b.len() as int))
    }
}

proof fn dot_product_consistency(a1: Seq<f32>, a2: Seq<f32>, b1: Seq<f32>, b2: Seq<f32>)
    requires a1 =~= a2 && b1 =~= b2 && a1.len() == b1.len()
    ensures dot_product(a1, b1) == dot_product(a2, b2)
{
}

spec fn view_col(B: Seq<Seq<f32>>, j: int) -> Seq<f32> 
    requires 0 <= j < B[0].len(), B.len() > 0
    ensures result.len() == B.len()
{
    Seq::new(B.len(), |i| B[i][j])
}
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
/* code modified by LLM (iteration 5): Fixed result variable declaration and verification */
{
    let mut result = Vec::new();
    let m = A.len();
    let n = B.len();
    let p = if n > 0 { B[0].len() } else { 0 };
    
    proof {
        matrix_dimensions_consistent(A);
        matrix_dimensions_consistent(B);
    }
    
    let mut i: usize = 0;
    while i < m
        invariant
            0 <= i <= m,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k].len() == p,
        decreases m - i
    {
        let mut row = Vec::new();
        let mut j: usize = 0;
        while j < p
            invariant
                0 <= j <= p,
                row.len() == j,
                forall|k: int| 0 <= k < j ==> (#[trigger] row[k]) is f32,
            decreases p - j
        {
            let mut sum = 0.0;
            let mut k: usize = 0;
            while k < n
                invariant
                    0 <= k <= n,
                    sum == dot_product(A@[i].subrange(0, k as int), view_col(B@, j as int).subrange(0, k as int)),
                decreases n - k
            {
                sum += A[i][k] * B[k][j];
                k += 1;
            }
            row.push(sum);
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}