// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed predicate syntax with semicolon */
predicate is_matrix(m: Vec<Vec<i8>>, rows: int, cols: int) {
    rows > 0 && cols > 0 &&
    m.len() as int == rows &&
    forall|i: int| 0 <= i < rows ==> (#[trigger] m@[i]).len() as int == cols
}

proof fn dot_product_proof(a: Seq<i8>, b: Seq<i8>) -> (sum: i8)
    requires
        a.len() == b.len(),
        a.len() > 0,
    ensures
        |sum| <= (a.len() as i8) * 127 * 127
{
    if a.len() == 1 {
        a[0] * b[0]
    } else {
        let rest_sum = dot_product_proof(a.subrange(1, a.len() as int), b.subrange(1, b.len() as int));
        a[0] * b[0] + rest_sum
    }
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
/* code modified by LLM (iteration 5): Implement matrix multiplication with proper bounds and verification */
{
    let rows = A.len();
    let cols = B@[0].len();
    let inner_dim = B.len();
    
    let mut result: Vec<Vec<i8>> = Vec::new();
    
    let mut i: usize = 0;
    while i < rows
        invariant
            i <= rows,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] result@[j]).len() == cols
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        
        while j < cols
            invariant
                j <= cols,
                row.len() == j,
                forall|k: int| 0 <= k < j ==> |row@[k]| <= (inner_dim as i8) * 127 * 127
        {
            let mut sum: i8 = 0;
            let mut k: usize = 0;
            
            while k < inner_dim
                invariant
                    k <= inner_dim,
                    |sum| <= (k as i8) * 127 * 127
            {
                sum = sum + A[i][k] * B[k][j];
                k = k + 1;
            }
            
            row.push(sum);
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